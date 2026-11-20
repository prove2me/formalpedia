-- Prove2me | solution 1 for RAREPricing.Existence.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-19T08:08:16.236162+00:00
-- url     : https://prove2.me/submissions/f3b28eb9-880f-4472-99d0-638e0af18692

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

open RAREPricing RAREPricing.Existence

namespace P2MHole01_5ba50a15
theorem solution {n m : ℕ} (M : Market n m) (i : Fin n) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
  (hp : (0 : Fin m → ℝ) ≤ p) (hx : x i ∈ demandBuyer M p i) :
  ∑ j : Fin m, p j * x i j = min (M.b i) (∑ j : Fin m, p j) := by
  set z := x i with hz_def
  have hz_cube : z ∈ cube m := (hx.1).1
  have hz_cost : ∑ j, p j * z j ≤ M.b i := (hx.1).2
  have hmax : ∀ z' ∈ budgetSet M p i, M.u i z' ≤ M.u i z := hx.2
  have hsmo : StrictMonoOn (M.u i) (cube m) := M.u_strictMonoOn i
  have hz0 : ∀ k, 0 ≤ z k := (Pi.le_def.mp hz_cube.1)
  have hz1 : ∀ k, z k ≤ 1 := (Pi.le_def.mp hz_cube.2)
  have hzle : z ≤ 1 := by
    rw [Pi.le_def]
    intro k
    exact hz1 k
  have hc1 : 1 ∈ cube m := by
    rw [cube, Set.mem_Icc, Pi.le_def, Pi.le_def]
    exact ⟨fun k => by norm_num, fun k => by norm_num⟩
  let S := ∑ j : Fin m, p j
  have hcost1 : (∑ j : Fin m, p j * (1 : Fin m → ℝ) j) = S := by
    simp [mul_one]
    rfl
  have hS_b : S ≤ M.b i → 1 ∈ budgetSet M p i := fun hs => ⟨hc1, hcost1 ▸ hs⟩
  by_cases hcase : S ≤ M.b i
  · have hu1 : M.u i 1 ≤ M.u i z := hmax 1 (hS_b hcase)
    have hne : ¬ z < 1 := by
      intro hlt
      have hltu : M.u i z < M.u i 1 := by
        apply hsmo <;> assumption
      linarith
    rcases lt_or_eq_of_le hzle with hlt | hz1
    · exact absurd hlt hne
    · rw [hz1]
      simp [mul_one]
      exact hcase
  · have hb : M.b i ≤ S := (not_le.mp hcase).le
    by_contra hnz
    have hltc : ∑ j, p j * z j < M.b i := by
      by_contra hnot
      have heq : ∑ j, p j * z j = M.b i := le_antisymm hz_cost (not_lt.mp hnot)
      exact hnz (heq.trans (min_eq_left hb).symm)
    have hexist : ∃ j, p j > 0 ∧ z j < 1 := by
      by_contra hn2
      have hall : ∀ j, p j > 0 → z j = 1 := by
        intro j hjp
        by_contra hnzj
        exact hn2 ⟨j, ⟨hjp, lt_of_le_of_ne (hz1 j) hnzj⟩⟩
      have hcS : ∑ j : Fin m, p j * z j = ∑ j : Fin m, p j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hjp : p j > 0
        · rw [hall j hjp]
          ring
        · have : p j = 0 := le_antisymm (le_of_not_gt hjp) (hp j)
          rw [this]
          ring
      have hge : M.b i ≤ ∑ j : Fin m, p j * z j := by
        calc
          M.b i ≤ S := hb
          _ = ∑ j : Fin m, p j := by rfl
          _ = ∑ j : Fin m, p j * z j := hcS.symm
      linarith [hge, hltc]
    rcases hexist with ⟨j, hjp, hzt⟩
    set c := ∑ k : Fin m, p k * z k with hc_def
    have htc : c < M.b i := by simpa [hc_def] using hltc
    set t := min (1 - z j) ((M.b i - c) / p j) with ht_def
    have htp : 0 < t := by
      rw [ht_def]
      exact lt_min (sub_pos.mpr hzt) (div_pos (sub_pos.mpr htc) hjp)
    have ht1z : t ≤ 1 - z j := by
      rw [ht_def]
      exact min_le_left _ _
    have htgap : p j * t ≤ M.b i - c := by
      rw [ht_def]
      calc
        p j * min (1 - z j) ((M.b i - c) / p j) =
            min (p j * (1 - z j)) (p j * ((M.b i - c) / p j)) := by
          rw [mul_min_of_nonneg (1 - z j) ((M.b i - c) / p j) hjp.le]
        _ ≤ p j * ((M.b i - c) / p j) := min_le_right _ _
        _ = M.b i - c := by
          exact mul_div_cancel₀ (M.b i - c) (ne_of_gt hjp)
    set z' := fun k : Fin m => if k = j then z j + t else z k with hzp_def
    have hzp_cube : z' ∈ cube m := by
      rw [cube, Set.mem_Icc, Pi.le_def, Pi.le_def]
      constructor
      · intro k
        simp [hzp_def]
        split_ifs with hk
        · linarith [hz0 j, htp]
        · exact hz0 k
      · intro k
        simp [hzp_def]
        split_ifs with hk
        · calc
            z j + t ≤ z j + (1 - z j) := add_le_add_right ht1z (z j)
            _ = 1 := by ring
        · exact hz1 k
    have hsum : ∑ k, p k * z' k = c + p j * t := by
      have hdif : ∀ k, z' k - z k = (if k = j then t else 0 : ℝ) := by
        intro k
        by_cases hk : k = j
        · simp [hzp_def, hk]
        · simp [hzp_def, hk]
      calc
        (∑ k, p k * z' k) = ∑ k, p k * (z k + (z' k - z k)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = ∑ k, (p k * z k + p k * (z' k - z k)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = ∑ k, p k * z k + ∑ k, p k * (z' k - z k) := by
          rw [Finset.sum_add_distrib]
        _ = c + ∑ k, p k * (z' k - z k) := by rw [hc_def]
        _ = c + ∑ k, p k * (if k = j then t else 0) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [hdif k]
        _ = c + p j * t := by
          congr 1
          have hA : (∑ k : Fin m, p k * (if k = j then t else 0 : ℝ)) =
              (∑ k : Fin m, (if k = j then p k * t else 0 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : k = j
            · simp [hk]
            · simp [hk]
          have hB : (∑ k : Fin m, (if k = j then p k * t else 0 : ℝ)) = p j * t :=
            Fintype.sum_ite_eq' j (fun k => p k * t)
          exact hA.trans hB
    have hzp_cost : ∑ k, p k * z' k ≤ M.b i := by
      rw [hsum]
      calc
        c + p j * t ≤ c + (M.b i - c) := add_le_add_right htgap c
        _ = M.b i := by ring
    have hle' : z ≤ z' := by
      rw [Pi.le_def]
      intro k
      simp [hzp_def]
      split_ifs with hk
      · rw [hk]
        exact le_add_of_nonneg_right htp.le
      · rfl
    have hzpj : z' j = z j + t := by
      simp [hzp_def]
    have hne' : z ≠ z' := by
      intro hnz
      have heq : z' j = z j := by rw [← hnz]
      linarith [heq, hzpj]
    have hlt' : z < z' := lt_of_le_of_ne hle' hne'
    have hzp_b : z' ∈ budgetSet M p i := ⟨hzp_cube, hzp_cost⟩
    have hcontra : M.u i (z') > M.u i z := by
      apply hsmo <;> assumption
    linarith [hmax z' hzp_b, hcontra]
end P2MHole01_5ba50a15

/- Non-rivalrous: a demanded bundle of buyer i satisfies pᵀ(x i) = min (b_i) (∑ p). -/
theorem nr_buyer_eq {n m : ℕ} (M : Market n m) (i : Fin n) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hp : 0 ≤ p) (hx : x i ∈ demandBuyer M p i) :
    ∑ j, p j * x i j = min (M.b i) (∑ j, p j) := by
  (first | exact P2MHole01_5ba50a15.solution M i p x hp hx | (apply P2MHole01_5ba50a15.solution <;> assumption))

namespace P2MHole02_2234c0ab
/-- A non-rivalrous demanded bundle `z` of buyer `i` (with `p ≥ 0`) spends exactly
`min (b_i, ∑_j p_j)`: at most the budget and at most the total price (since `z ∈ [0,1]^m`),
and strictly less would contradict the maximality of `z` (moving `z` slightly toward `1`
stays in the budget set and strictly increases `u_i`, since `u_i` is strictly monotone). -/
lemma spend_eq {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (hp : 0 ≤ p) (i : Fin n) (z : Fin m → ℝ)
    (hzcube : z ∈ cube m) (hzbud : ∑ j : Fin m, p j * z j ≤ M.b i)
    (hmax : ∀ z' ∈ budgetSet M p i, M.u i z' ≤ M.u i z) :
    ∑ j : Fin m, p j * z j = min (M.b i) (∑ j : Fin m, p j) := by
  have hz0 : 0 ≤ z ∧ z ≤ 1 := by simpa [cube] using hzcube
  have hzj : ∀ j, 0 ≤ z j ∧ z j ≤ 1 := fun j => ⟨hz0.1 j, hz0.2 j⟩
  -- upper bound: p·z ≤ b_i and p·z ≤ ∑ p
  have hterm : ∀ j, p j * z j ≤ p j := fun j => by
    simpa using mul_le_mul_of_nonneg_left (hzj j).2 (hp j)
  have hsp_le_s1 : ∑ j, p j * z j ≤ ∑ j, p j :=
    Finset.sum_le_sum fun j _ => hterm j
  have hupper : ∑ j, p j * z j ≤ min (M.b i) (∑ j, p j) :=
    le_min_iff.mpr ⟨hzbud, hsp_le_s1⟩
  -- lower bound: p·z < min(b_i, ∑ p) contradicts maximality
  have hlower : min (M.b i) (∑ j, p j) ≤ ∑ j, p j * z j := by
    by_contra hlt
    have hltb : ∑ j, p j * z j < M.b i := by
      by_contra h
      exact hlt (le_trans (min_le_left (M.b i) _) (not_lt.mp h))
    have hlt1 : ∑ j, p j * z j < ∑ j, p j := by
      by_contra h
      exact hlt (le_trans (min_le_right (M.b i) _) (not_lt.mp h))
    -- p·(1 - z) > 0, so for some j we have p_j > 0 and z_j < 1
    have hs1z_eq : ∑ j, p j * (1 - z j) = (∑ j, p j) - ∑ j, p j * z j := by
      calc
        (∑ j : Fin m, p j * (1 - z j)) = ∑ j, (p j - p j * z j) := by
          simp only [mul_sub]; congr; funext j; ring
        _ = (∑ j, p j) - ∑ j, p j * z j := by simp only [Finset.sum_sub_distrib]
    have hs1z_pos : 0 < ∑ j, p j * (1 - z j) := by
      rw [hs1z_eq]
      exact sub_pos.mpr hlt1
    have hs1z_nneg : ∀ j, 0 ≤ p j * (1 - z j) := fun j => mul_nonneg (hp j) (sub_nonneg.mpr (hzj j).2)
    have hj : ∃ j, 0 < p j * (1 - z j) := by
      by_contra h0
      push_neg at h0
      have hj0 : ∀ j, p j * (1 - z j) = 0 :=
        fun j => le_antisymm (h0 j) (hs1z_nneg j)
      have hsum0 : ∑ j, p j * (1 - z j) = 0 := Finset.sum_eq_zero (fun j _ => hj0 j)
      rw [hsum0] at hs1z_pos
      linarith
    obtain ⟨j, hjjpos⟩ := hj
    have hjj1 : 0 < 1 - z j := by
      by_contra h
      have h1z : 1 - z j ≤ 0 := not_lt.mp h
      have hprod : p j * (1 - z j) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hp j) h1z
      linarith
    -- step t = min(1, (b_i - p·z) / p·(1 - z)) / 2 : 0 < t ≤ 1 and t·p·(1 - z) < b_i - p·z
    set hbud := M.b i - ∑ k, p k * z k with hbud_def
    have hbud_pos : 0 < hbud := sub_pos.mpr hltb
    set sstar := hbud / (∑ j, p j * (1 - z j)) with sstar_def
    have hsstar_pos : 0 < sstar := div_pos hbud_pos hs1z_pos
    set t := min 1 sstar / 2 with t_def
    have htpos : 0 < t := by
      rw [t_def]
      exact half_pos (lt_min_iff.mpr ⟨by norm_num, hsstar_pos⟩)
    have ht1 : t ≤ 1 := by
      rw [t_def]
      exact (div_le_one (by norm_num)).mpr (le_trans (min_le_left 1 sstar) (by norm_num))
    have hts : t < sstar := by
      rw [t_def]
      have h1 : min 1 sstar / 2 ≤ sstar / 2 :=
        (div_le_div_iff_of_pos_right (by norm_num)).mpr (min_le_right 1 sstar)
      have h2 : sstar / 2 < sstar := div_lt_self hsstar_pos (by norm_num)
      exact lt_of_le_of_lt h1 h2
    have hinc : t * (∑ j, p j * (1 - z j)) < hbud := by
      rw [sstar_def] at hts
      exact (lt_div_iff₀ hs1z_pos).mp hts
    -- z' = z + t·(1 - z) is in the cube, in the budget set, and z ≤ z' with z ≠ z
    set z' : Fin m → ℝ := fun j => z j + t * (1 - z j) with z'_def
    have hz'cube : z' ∈ cube m := by
      constructor
      · intro j
        exact add_nonneg (hzj j).1 (mul_nonneg htpos.le (sub_nonneg.mpr (hzj j).2))
      · intro j
        have h1mz : 0 ≤ 1 - z j := sub_nonneg.mpr (hzj j).2
        have ht1mz : t * (1 - z j) ≤ 1 - z j := by simpa using mul_le_mul_of_nonneg_right ht1 h1mz
        calc
          z j + t * (1 - z j) ≤ z j + (1 - z j) := add_le_add_right ht1mz (z j)
          _ = 1 := by ring
    have hexp : ∑ j, p j * z' j = ∑ j, (p j * z j + t * p j * (1 - z j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [z'_def, mul_add]
      ring
    have hsumassoc : ∑ j, t * p j * (1 - z j) = ∑ j, t * (p j * (1 - z j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h2 : ∑ j, (p j * z j + t * p j * (1 - z j)) =
        ∑ j, p j * z j + t * ∑ j, p j * (1 - z j) := by
      rw [Finset.sum_add_distrib, hsumassoc, Finset.mul_sum]
    have hlt' : ∑ j, (p j * z j + t * p j * (1 - z j)) < ∑ j, p j * z j + hbud := by
      calc ∑ j, (p j * z j + t * p j * (1 - z j))
          = ∑ j, p j * z j + t * ∑ j, p j * (1 - z j) := h2
          _ < ∑ j, p j * z j + hbud := add_lt_add_right hinc (∑ j, p j * z j)
    have hz'bud_lt : ∑ j, p j * z' j < M.b i := by
      calc ∑ j, p j * z' j
          = ∑ j, (p j * z j + t * p j * (1 - z j)) := hexp
          _ < ∑ j, p j * z j + hbud := hlt'
          _ = M.b i := by rw [hbud_def]; ring
    have hz'bud : ∑ j, p j * z' j ≤ M.b i := hz'bud_lt.le
    have hz'budset : z' ∈ budgetSet M p i := by
      rw [budgetSet]
      exact ⟨hz'cube, hz'bud⟩
    have hmax' : M.u i z' ≤ M.u i z := hmax z' hz'budset
    have hz_le_z' : z ≤ z' := by
      intro j
      exact le_add_of_nonneg_right (mul_nonneg htpos.le (sub_nonneg.mpr (hzj j).2))
    have hz_ne_z' : z ≠ z' := by
      have hj'pos : 0 < t * (1 - z j) := mul_pos htpos hjj1
      intro h
      rw [z'_def] at h
      have hne : z j = z j + t * (1 - z j) := congr_fun h j
      have : t * (1 - z j) = 0 := add_eq_left.mp hne.symm
      exact ne_of_gt hj'pos this
    have hstrict : M.u i z < M.u i z' :=
      M.u_strictMonoOn i hzcube hz'cube (lt_of_le_of_ne hz_le_z' hz_ne_z')
    exact lt_irrefl (M.u i z) (lt_of_lt_of_le hstrict hmax')
  exact le_antisymm hupper hlower

theorem solution {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
  (hp : (0 : Fin m → ℝ) ≤ p) (hx : x ∈ DemNR M p) :
  totalRevenue p x = ∑ i : Fin n, min (M.b i) (∑ j : Fin m, p j) := by
  have hx' : ∀ i, x i ∈ demandBuyer M p i := by simpa [DemNR] using hx
  calc
    totalRevenue p x
      = ∑ j, p j * ∑ i, x i j := by simp only [totalRevenue, revenue]
    _ = ∑ j, ∑ i, p j * x i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, p j * x i j := by rw [Finset.sum_comm]
    _ = ∑ i, min (M.b i) (∑ j : Fin m, p j) := by
      apply Finset.sum_congr rfl
      intro i _
      obtain ⟨hxiB, hxiMax⟩ : x i ∈ budgetSet M p i ∧
          ∀ z' ∈ budgetSet M p i, M.u i z' ≤ M.u i (x i) := by simpa [demandBuyer] using hx' i
      obtain ⟨hxiCube, hxiBud⟩ : x i ∈ cube m ∧ ∑ j, p j * x i j ≤ M.b i := by
        simpa [budgetSet] using hxiB
      exact spend_eq M p hp i (x i) hxiCube hxiBud hxiMax
end P2MHole02_2234c0ab

/- Non-rivalrous: total revenue of any demanded allocation depends only on ∑ p. -/
theorem nr_total_eq {n m : ℕ} (M : Market n m) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hp : 0 ≤ p) (hx : x ∈ DemNR M p) :
    totalRevenue p x = ∑ i, min (M.b i) (∑ j, p j) := by
  (first | exact P2MHole02_2234c0ab.solution M p x hp hx | (apply P2MHole02_2234c0ab.solution <;> assumption))

namespace P2MHole03_a1772ddc
theorem solution {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
  (hp : (0 : Fin m → ℝ) ≤ p) (hx : x ∈ AffR M p) : totalRevenue p x ≤ min (∑ j : Fin m, p j) M.totalBudget := by
  obtain ⟨hcube, hsupply, hbud⟩ := hx
  -- Bound 1: ∑_j p_j (∑_i x_ij) ≤ ∑_j p_j, since ∑_i x_ij ≤ 1 and p_j ≥ 0.
  have h1 : totalRevenue p x ≤ ∑ j : Fin m, p j := by
    unfold totalRevenue revenue
    refine Finset.sum_le_sum fun j _ => ?_
    simpa [mul_one] using mul_le_mul_of_nonneg_left (hsupply j) (hp j)
  -- Bound 2: totalRevenue = ∑_j p_j (∑_i x_ij) = ∑_i (∑_j p_j x_ij) ≤ ∑_i b_i.
  have h2 : totalRevenue p x ≤ M.totalBudget := by
    unfold totalRevenue revenue Market.totalBudget
    have heq : (∑ j : Fin m, p j * ∑ i : Fin n, x i j) = (∑ i : Fin n, ∑ j : Fin m, p j * x i j) := by
      calc
        _ = ∑ j : Fin m, ∑ i : Fin n, p j * x i j := by
          congr
          funext j
          rw [Finset.mul_sum]
        _ = ∑ i : Fin n, ∑ j : Fin m, p j * x i j := by
          rw [Finset.sum_comm]
    rw [heq]
    exact Finset.sum_le_sum fun i _ => hbud i
  -- Combine.
  exact le_min h1 h2
end P2MHole03_a1772ddc

/- Rivalrous: every affordable allocation earns at most min (∑ p) B. -/
theorem r_rev_le {n m : ℕ} (M : Market n m) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hp : 0 ≤ p) (hx : x ∈ AffR M p) :
    totalRevenue p x ≤ min (∑ j, p j) M.totalBudget := by
  (first | exact P2MHole03_a1772ddc.solution M p x hp hx | (apply P2MHole03_a1772ddc.solution <;> assumption))

namespace P2MHole04_37485e2f
theorem solution {n m : ℕ} (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) (hp : (0 : Fin m → ℝ) ≤ p)
  (hS : ∀ (j : Fin m), (0 : ℝ) ≤ ∑ i : Fin n, x i j ∧ ∑ i : Fin n, x i j ≤ (1 : ℝ))
  (hlt : ∑ j : Fin m, p j * ∑ i : Fin n, x i j < ∑ j : Fin m, p j) :
  ∃ (j : Fin m), (0 : ℝ) < p j ∧ ∑ i : Fin n, x i j < (1 : ℝ) := by
  let s : Fin m → ℝ := fun j => ∑ i : Fin n, x i j
  by_contra h
  -- h : ¬ ∃ j, 0 < p j ∧ s j < 1, so 0 < p j forces s j ≥ 1.
  have hh : ∀ j, 0 < p j → 1 ≤ s j := by
    intro j hpj
    apply not_lt.mp
    intro hlt_s
    exact h ⟨j, ⟨hpj, hlt_s⟩⟩
  -- For each j, either p j = 0 or s j = 1, so p j * s j = p j.
  have hterm : ∀ j, p j * s j = p j := by
    intro j
    by_cases hpj : 0 < p j
    · have hs_eq1 : s j = 1 := le_antisymm (hS j).2 (hh j hpj)
      rw [hs_eq1]
      ring
    · have hpj0 : p j = 0 := (le_antisymm (hp j) (not_lt.mp hpj)).symm
      rw [hpj0]
      ring
  have hsum : ∑ j : Fin m, p j * s j = ∑ j : Fin m, p j := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [hsum] at hlt
  exact lt_irrefl _ hlt
end P2MHole04_37485e2f

/- With per-buyer shares in [0, 1], a strict revenue deficit versus the price sum
    localizes: some good with a positive price is not fully used. -/
theorem r_lt_implies_gap {n m : ℕ} (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
    (hp : 0 ≤ p) (hS : ∀ j, 0 ≤ ∑ i, x i j ∧ ∑ i, x i j ≤ 1)
    (hlt : ∑ j, p j * ∑ i, x i j < ∑ j, p j) :
    ∃ j, 0 < p j ∧ ∑ i, x i j < 1 := by
  (first | exact P2MHole04_37485e2f.solution p x hp hS hlt | (apply P2MHole04_37485e2f.solution <;> assumption))

namespace P2MHole05_a517213c
/- Increase one buyer's bundle in one good that still has slack: keep it in `[0,1]^m`,
   keep the unit supplies and the budgets, and strictly improve that buyer's utility. -/
theorem solution {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
  (hp : (0 : Fin m → ℝ) ≤ p) (hx : x ∈ AffR M p) (hgap : ∃ (j : Fin m), (0 : ℝ) < p j ∧ ∑ i : Fin n, x i j < (1 : ℝ))
  (hslack : ∃ (i : Fin n), ∑ j : Fin m, p j * x i j < M.b i) : ∃ y ∈ AffR M p, ParetoDominates M y x := by
  obtain ⟨j, hjp, hgj⟩ := hgap
  obtain ⟨i, hislack⟩ := hslack
  have hxcube : ∀ i', x i' ∈ cube m := hx.1
  have hxsupp : ∀ k, ∑ i', x i' k ≤ 1 := hx.2.1
  have hxbud : ∀ i', ∑ k, p k * x i' k ≤ M.b i' := hx.2.2
  have hgap0 : 0 < 1 - ∑ i', x i' j := by
    rw [sub_pos]
    exact hgj
  have hbgap : 0 < M.b i - ∑ k, p k * x i k := by
    rw [sub_pos]
    exact hislack
  set ε := min ((1 - ∑ i', x i' j) / 2) ((M.b i - ∑ k, p k * x i k) / (p j * 2)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (half_pos hgap0) (div_pos hbgap (mul_pos hjp (by norm_num)))
  have hεle_gap : ε ≤ 1 - ∑ i', x i' j := by
    rw [hεdef]
    exact le_trans (min_le_left _ _) (half_le_self (le_of_lt hgap0))
  have hεle_b : ε ≤ (M.b i - ∑ k, p k * x i k) / (p j * 2) := by
    rw [hεdef]
    exact min_le_right _ _
  have hpe : p j * ε ≤ M.b i - ∑ k, p k * x i k := by
    calc p j * ε ≤ p j * ((M.b i - ∑ k, p k * x i k) / (p j * 2)) :=
      mul_le_mul_of_nonneg_left hεle_b (le_of_lt hjp)
      _ = (M.b i - ∑ k, p k * x i k) / 2 := by
        field_simp [hjp.ne']
        <;> ring
      _ ≤ M.b i - ∑ k, p k * x i k :=
        half_le_self (le_of_lt hbgap)
  set y : Fin n → Fin m → ℝ := fun i' k =>
      if i' = i then (if k = j then x i' k + ε else x i' k) else x i' k with hydef
  -- pointwise facts about y
  have hyneq : ∀ i', i' ≠ i → y i' = x i' := by
    intro i' hi'
    ext k
    by_cases hk : k = j
    · simp [y, hi']
    · simp [y, hi']
  have hsumite (c : ℝ) (hc : 0 < c) : ∑ i' : Fin n, (if i' = i then c else 0) = c := by
    rw [Finset.sum_eq_single (a := i) (s := (Finset.univ : Finset (Fin n))) (f := fun i' => if i' = i then c else 0)
        (fun i' _ hne => by
          by_cases hi'' : i' = i
          · exfalso; exact hne hi''
          · simp [hi''])
        (by
          intro h
          exfalso
          apply h
          exact Finset.mem_univ i)]
    simp
  have hsumite2 (c : ℝ) (hc : 0 < c) : ∑ k : Fin m, (if k = j then c else 0) = c := by
    rw [Finset.sum_eq_single (a := j) (s := (Finset.univ : Finset (Fin m))) (f := fun k => if k = j then c else 0)
        (fun k _ hne => by
          by_cases hj' : k = j
          · exfalso; exact hne hj'
          · simp [hj'])
        (by
          intro h
          exfalso
          apply h
          exact Finset.mem_univ j)]
    simp
  have hy : y ∈ AffR M p := by
    dsimp [AffR, cube, y]
    refine ⟨?_, ?_, ?_⟩
    · intro i'
      refine ⟨fun k => ?_, fun k => ?_⟩
      · by_cases hi' : i' = i
        · by_cases hk : k = j
          · simp [hi', hk]
            have h0ij : 0 ≤ x i j := (hxcube i).1 j
            linarith [h0ij, hεpos]
          · simp [hi', hk]
            exact (hxcube i).1 k
        · by_cases hk : k = j
          · simp [hi', hk]
            exact (hxcube i').1 j
          · simp [hi', hk]
            exact (hxcube i').1 k
      · by_cases hi' : i' = i
        · by_cases hk : k = j
          · simp [hi', hk]
            have hxijsupp : x i j ≤ ∑ i'', x i'' j := by
              rw [← hi']
              exact Finset.single_le_sum (f := fun i'' => x i'' j) (fun i'' _ => (hxcube i'').1 j)
                (Finset.mem_univ i')
            linarith [hxijsupp, hεle_gap]
          · simp [hi', hk]
            exact (hxcube i).2 k
        · by_cases hk : k = j
          · simp [hi', hk]
            exact (hxcube i').2 j
          · simp [hi', hk]
            exact (hxcube i').2 k
    · intro k
      by_cases hk : k = j
      · have hyk' : ∀ i', y i' k = x i' k + (if i' = i then ε else 0) := by
          intro i'
          by_cases hi' : i' = i
          · simp [y, hi', hk]
          · simp [y, hi', hk]
        calc (∑ i', y i' k) = (∑ i', (x i' k + (if i' = i then ε else 0))) := by
              rw [Finset.sum_congr rfl (fun i' _ => hyk' i')]
            _ = (∑ i', x i' k + ε) := by rw [Finset.sum_add_distrib, hsumite ε hεpos]
            _ ≤ 1 := by rw [hk]; linarith [hxsupp j, hεle_gap]
      · have hyk : ∀ i', y i' k = x i' k := by
          intro i'
          by_cases hi' : i' = i
          · simp [y, hi', hk]
          · simp [y, hi']
        rw [Finset.sum_congr rfl (fun i' _ => hyk i')]
        exact hxsupp k
    · intro i'
      by_cases hi' : i' = i
      · rw [hi']
        have hb : ∀ k, p k * y i k = p k * x i k + (if k = j then p j * ε else 0) := by
          intro k
          by_cases hk : k = j
          · simp [y, hk, mul_add]
          · simp [y, hk]
        calc ∑ k, p k * y i k
            = (∑ k, p k * x i k + p j * ε) := by
              rw [Finset.sum_congr rfl (fun k _ => hb k), Finset.sum_add_distrib,
                hsumite2 (p j * ε) (mul_pos hjp hεpos)]
            _ ≤ M.b i := by linarith [hxbud i, hpe]
      · simpa [hi'] using hxbud i'
  have hycube : y i ∈ cube m := (hy.1) i
  have hxy : x i ≤ y i := by
    intro k
    by_cases hk : k = j
    · simp [y, hk]
      exact le_of_lt hεpos
    · simp [y, hk]
  have hne : x i ≠ y i := by
    intro h
    have h := congr_fun h j
    simp [y] at h
    linarith [hεpos]
  have hud : ∀ i', M.u i' (x i') ≤ M.u i' (y i') := by
    intro i'
    by_cases hi' : i' = i
    · rw [hi']
      exact le_of_lt (M.u_strictMonoOn i (a := x i) (b := y i) (hxcube i) hycube
          (lt_of_le_of_ne hxy hne))
    · have hyeq : y i' = x i' := hyneq i' hi'
      rw [hyeq]
  have hudst : M.u i (x i) < M.u i (y i) :=
    M.u_strictMonoOn i (a := x i) (b := y i) (hxcube i) hycube (lt_of_le_of_ne hxy hne)
  exact ⟨y, hy, ⟨hud, ⟨i, hudst⟩⟩⟩
end P2MHole05_a517213c

/- Giving a buyer with budget slack a small extra amount of an underused good with
    a positive price stays affordable and Pareto-dominates. -/
theorem r_slack_dominates {n m : ℕ} (M : Market n m) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hp : 0 ≤ p) (hx : x ∈ AffR M p)
    (hgap : ∃ j, 0 < p j ∧ ∑ i, x i j < 1)
    (hslack : ∃ i, ∑ j, p j * x i j < M.b i) :
    ∃ y, y ∈ AffR M p ∧ ParetoDominates M y x := by
  (first | exact P2MHole05_a517213c.solution M p x hp hx hgap hslack | (apply P2MHole05_a517213c.solution <;> assumption))

namespace P2MHole06_98c952d0
theorem solution {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
  (hb : ∀ (i : Fin n), ∑ j : Fin m, p j * x i j = M.b i) : totalRevenue p x = M.totalBudget := by
  calc
    totalRevenue p x = ∑ j : Fin m, p j * ∑ i : Fin n, x i j := rfl
    _ = ∑ j : Fin m, ∑ i : Fin n, p j * x i j := by simp [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin m, p j * x i j := by rw [Finset.sum_comm]
    _ = ∑ i : Fin n, M.b i := Finset.sum_congr rfl (fun i _ => hb i)
    _ = M.totalBudget := rfl
end P2MHole06_98c952d0

/- If every buyer spends her whole budget, revenue is the total budget. -/
theorem r_binding_eq_B {n m : ℕ} (M : Market n m) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hb : ∀ i, ∑ j, p j * x i j = M.b i) :
    totalRevenue p x = M.totalBudget := by
  (first | exact P2MHole06_98c952d0.solution M p x hb | (apply P2MHole06_98c952d0.solution <;> assumption))

namespace P2MHole07_053242aa
open Finset

set_option autoImplicit false

theorem solution {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ)
    (hp : (0 : Fin m → ℝ) ≤ p) (hx : x ∈ DemR M p) :
    min (∑ j : Fin m, p j) M.totalBudget ≤ totalRevenue p x := by
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : totalRevenue p x < min (∑ j, p j) M.totalBudget
  have hRlt : totalRevenue p x < ∑ j : Fin m, p j := by
    simpa using lt_of_lt_of_le hcontra (min_le_left _ _)
  have hRltB : totalRevenue p x < M.totalBudget := by
    simpa using lt_of_lt_of_le hcontra (min_le_right _ _)
  unfold DemR PO at hx
  obtain ⟨haff, hpo⟩ := hx
  unfold AffR at haff
  obtain ⟨hxcube, hsupply, hbudget⟩ := haff
  -- hx i : 0 ≤ x i ≤ 1 pointwise; hsupply : ∑_i x_i_j ≤ 1; hbudget : c_i ≤ b_i
  have hnn : ∀ i : Fin n, ∀ j : Fin m, 0 ≤ x i j := by
    intro i j
    exact (Set.mem_Icc.mp (hxcube i)).1 j
  set c : Fin n → ℝ := fun i => ∑ j : Fin m, p j * x i j with hc
  set s : Fin m → ℝ := fun j => ∑ i : Fin n, x i j with hs
  have hrev_s : totalRevenue p x = ∑ j : Fin m, p j * s j := by
    simp only [totalRevenue, revenue, hs]
  have hcrev : ∑ i : Fin n, c i = totalRevenue p x := by
    calc ∑ i : Fin n, c i = ∑ i : Fin n, ∑ j : Fin m, p j * x i j := rfl
      _ = ∑ j : Fin m, ∑ i : Fin n, p j * x i j := Finset.sum_comm
      _ = ∑ j : Fin m, p j * ∑ i : Fin n, x i j :=
        Finset.sum_congr rfl (fun j _ => by rw [← Finset.mul_sum])
      _ = totalRevenue p x := by
        simp only [totalRevenue, revenue, hs]
  -- a buyer with budget slack
  have hslack : ∃ i : Fin n, c i < M.b i := by
    by_contra h
    push_neg at h
    have hsum : M.totalBudget ≤ ∑ i : Fin n, c i :=
      Finset.sum_le_sum fun i _ => h i
    have h1 : ∑ i : Fin n, c i < M.totalBudget := by
      calc ∑ i : Fin n, c i = totalRevenue p x := hcrev
        _ < M.totalBudget := hRltB
    linarith
  obtain ⟨ib, hbi⟩ := hslack
  -- a good that is not fully sold and has positive price
  have hgaps : ∑ j : Fin m, p j * (1 - s j) = ∑ j : Fin m, p j - totalRevenue p x := by
    calc ∑ j : Fin m, p j * (1 - s j)
        = ∑ j : Fin m, (p j - p j * s j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j : Fin m, p j - ∑ j : Fin m, p j * s j := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ j : Fin m, p j - totalRevenue p x := by
            rw [hrev_s]
  have hgaps' : 0 < ∑ j : Fin m, p j * (1 - s j) := by
    simpa [hgaps] using sub_pos_of_lt hRlt
  have hgap : ∃ j : Fin m, 0 < p j * (1 - s j) := by
    by_contra h
    push_neg at h
    have hnn' : ∀ j : Fin m, 0 ≤ p j * (1 - s j) := by
      intro j
      exact mul_nonneg (hp j) (sub_nonneg.mpr (by simpa [hs] using hsupply j))
    have hzero : ∀ j : Fin m, p j * (1 - s j) = 0 :=
      fun j => le_antisymm (h j) (hnn' j)
    have hsum : ∑ j : Fin m, p j * (1 - s j) = 0 := by
      simpa using Finset.sum_congr rfl (fun j _ => hzero j)
    have hpos : 0 < ∑ j : Fin m, p j * (1 - s j) := by
      simpa [hgaps] using sub_pos_of_lt hRlt
    linarith
  obtain ⟨jb, hgj⟩ := hgap
  have hppj : 0 < p jb := by
    by_contra h
    have h1 : p jb * (1 - s jb) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr (by
        simpa [hs] using hsupply jb))
    have h2 : 0 < p jb * (1 - s jb) := hgj
    linarith
  have hss : s jb < 1 := by
    by_contra h
    have h1 : p jb * (1 - s jb) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hp jb) (sub_nonpos.mpr (by linarith))
    have h2 : 0 < p jb * (1 - s jb) := hgj
    linarith
  -- pick a small epsilon
  have hxs : x ib jb ≤ s jb := Finset.single_le_sum (fun i _ => hnn i jb) (Finset.mem_univ _)
  set eps := min (min (1 - s jb) ((M.b ib - c ib) / p jb)) (1 - x ib jb) with heps
  have hepspos : 0 < eps :=
    lt_min (lt_min (sub_pos.mpr hss) (div_pos (sub_pos.mpr hbi) hppj))
      (sub_pos.mpr (lt_of_le_of_lt hxs hss))
  have heps1 : eps ≤ 1 - s jb := by
    have h1 : eps ≤ min (1 - s jb) ((M.b ib - c ib) / p jb) := min_le_left _ _
    have h2 : min (1 - s jb) ((M.b ib - c ib) / p jb) ≤ 1 - s jb := min_le_left _ _
    exact le_trans h1 h2
  have heps2 : eps ≤ (M.b ib - c ib) / p jb := by
    have h1 : eps ≤ min (1 - s jb) ((M.b ib - c ib) / p jb) := min_le_left _ _
    have h2 : min (1 - s jb) ((M.b ib - c ib) / p jb) ≤ (M.b ib - c ib) / p jb := min_le_right _ _
    exact le_trans h1 h2
  have heps3 : eps ≤ 1 - x ib jb := min_le_right _ _
  set y : Fin n → Fin m → ℝ := fun i j =>
      if i = ib then (if j = jb then x i j + eps else x i j) else x i j with hy
  have hycube : ∀ i : Fin n, y i ∈ cube m := by
    intro i
    refine Set.mem_Icc.mpr ⟨fun j => by
        by_cases hij : i = ib
        · by_cases hjj : j = jb
          · have h1 : 0 ≤ x ib jb + eps :=
              add_nonneg (hnn ib jb) (le_of_lt hepspos)
            simpa [y, hij, hjj] using h1
          · have h1 : 0 ≤ x ib j := by simpa [y, hij, hjj] using hnn ib j
            simpa [y, hij, hjj] using h1
        · have h1 : 0 ≤ x i j := by simpa [y, hij] using hnn i j
          simpa [y, hij] using h1
      , fun j => by
        by_cases hij : i = ib
        · by_cases hjj : j = jb
          · have h1 : x ib jb + eps ≤ 1 := by
              calc x ib jb + eps ≤ x ib jb + (1 - x ib jb) := add_le_add_right heps3 _
                _ = 1 := by ring
            simpa [y, hij, hjj] using h1
          · have h1 : x ib j ≤ 1 := (Set.mem_Icc.mp (hxcube ib)).2 j
            simpa [y, hij, hjj] using h1
        · have h1 : x i j ≤ 1 := (Set.mem_Icc.mp (hxcube i)).2 j
          simpa [y, hij] using h1⟩
  have hysupply : ∀ j : Fin m, ∑ i : Fin n, y i j ≤ 1 := by
    intro j
    by_cases hjj : j = jb
    · calc ∑ i : Fin n, y i j
          = ∑ i : Fin n, (if i = ib then x i j + eps else x i j) := by
            simpa [y, hjj]
        _ = ∑ i : Fin n, x i j + eps := by
            have h1 : (∑ i : Fin n, if i = ib then x i j + eps else x i j) =
                ∑ i : Fin n, (x i j + (if ib = i then eps else 0)) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hii : i = ib
              · simp only [hii, ite_true, ite_false]
              · have h2 : ¬ ib = i := fun h3 => hii h3.symm
                simp only [hii, h2, ite_true, ite_false, add_zero]
            rw [h1]
            have h2 : ∑ i : Fin n, (x i j + (if ib = i then eps else 0)) =
                ∑ i : Fin n, x i j + ∑ i : Fin n, (if ib = i then eps else 0) := by
              apply Finset.sum_add_distrib
            rw [h2]
            have h3 : ∑ i : Fin n, (if ib = i then eps else 0) = eps := by
              simp only [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) ib (fun _ => eps),
                Finset.mem_univ, ite_true]
            rw [h3]
          _ ≤ 1 := by
            have h1 : ∑ i : Fin n, x i j + eps = s jb + eps := by
              simp [s, hjj]
            have h2 : s jb + eps ≤ s jb + (1 - s jb) := add_le_add_right heps1 _
            have h3 : s jb + (1 - s jb) = 1 := by ring
            simpa [h1] using h2.trans (le_of_eq h3)
    · have h1 : ∑ i : Fin n, y i j = ∑ i : Fin n, x i j := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [y]
        by_cases hii : i = ib
        · simp only [hii, hjj, ite_true, ite_false]
        · simp only [hii, hjj, ite_true, ite_false]
      simpa [h1] using hsupply j
  have hybudget : ∀ i : Fin n, ∑ j : Fin m, p j * y i j ≤ M.b i := by
    intro i
    by_cases hij : i = ib
    · calc ∑ j : Fin m, p j * y i j
          = ∑ j : Fin m, p j * x ib j + p jb * eps := by
            simp only [y, hij, ite_true, ite_false]
            have h1 : ∑ j : Fin m, p j * (if j = jb then x ib j + eps else x ib j) =
                ∑ j : Fin m, (p j * x ib j + (if jb = j then p j * eps else 0)) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hjj : j = jb
              · simp only [hjj, mul_add, ite_true, add_zero]
              · have h2 : ¬ jb = j := fun h3 => hjj h3.symm
                simp only [hjj, h2, mul_add, ite_true, ite_false, add_zero]
            rw [h1]
            have h2 : ∑ j : Fin m, (p j * x ib j + (if jb = j then p j * eps else 0)) =
                ∑ j : Fin m, p j * x ib j + ∑ j : Fin m, (if jb = j then p j * eps else 0) := by
              apply Finset.sum_add_distrib
            rw [h2]
            have h3 : ∑ j : Fin m, (if jb = j then p j * eps else 0) = p jb * eps := by
              simp only [Finset.sum_ite_eq (Finset.univ : Finset (Fin m)) jb (fun j => p j * eps),
                Finset.mem_univ, ite_true]
            rw [h3]
          _ ≤ M.b ib := by
            have h1 : ∑ j : Fin m, p j * x ib j + p jb * eps = c ib + p jb * eps := by
              simp only [c]
            have h2 : p jb * eps ≤ M.b ib - c ib := by
              have h3 : p jb * eps ≤ p jb * ((M.b ib - c ib) / p jb) :=
                mul_le_mul_of_nonneg_left heps2 (le_of_lt hppj)
              have h4 : p jb * ((M.b ib - c ib) / p jb) = M.b ib - c ib := by
                field_simp [hppj.ne']
              exact h3.trans_eq h4
            have h3 : c ib + p jb * eps ≤ M.b ib := by
              linarith
            simpa [h1] using h3
          _ = M.b i := by simpa [hij]
    · calc ∑ j : Fin m, p j * y i j
          = ∑ j : Fin m, p j * x i j := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [y]
            by_cases hjj : j = jb
            · simp only [hjj, hij, ite_true, ite_false]
            · simp only [hjj, hij, ite_true, ite_false]
          _ ≤ M.b i := hbudget i
  have hyaff : y ∈ AffR M p := by
    unfold AffR
    exact ⟨fun i => by simpa using hycube i, fun j => by simpa using hysupply j,
      fun i => by simpa using hybudget i⟩
  have hstrict : M.u ib (x ib) < M.u ib (y ib) := by
    have hle : x ib ≤ y ib := by
      refine fun j => by
        by_cases hjj : j = jb
        · simp only [y, hjj, ite_true, ite_false]
          exact le_add_of_nonneg_right (le_of_lt hepspos)
        · simp only [y, hjj, ite_true, ite_false]
          exact le_rfl
    have hltj : x ib jb < y ib jb := by
      simp only [y, ite_true, ite_false]
      exact lt_add_of_pos_right _ hepspos
    exact M.u_strictMonoOn ib (hxcube ib) (hycube ib) (lt_of_le_of_ne hle (fun hne => by
      have h2 : x ib jb = y ib jb := by simpa [hne]
      exact (ne_of_lt hltj) h2))
  have hyPareto : ParetoDominates M y x := by
    unfold ParetoDominates
    refine ⟨fun i => by
        by_cases hij : i = ib
        · simpa [hij] using hstrict.le
        · have heq : y i = x i := by
            ext j
            simp only [y, hij, ite_true, ite_false]
          simpa [heq]
      , ⟨ib, hstrict⟩⟩
  exact hpo y hyaff hyPareto
end P2MHole07_053242aa

/- Rivalrous: every demanded (Pareto-optimal affordable) allocation earns
    at least min (∑ p) B. -/
theorem r_rev_ge {n m : ℕ} (M : Market n m) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hp : 0 ≤ p) (hx : x ∈ DemR M p) :
    min (∑ j, p j) M.totalBudget ≤ totalRevenue p x := by
  (first | exact P2MHole07_053242aa.solution M p x hp hx | (apply P2MHole07_053242aa.solution <;> assumption))

theorem solution {n m : ℕ} (M : Market n m) (s : Setting) (p q : Fin m → ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : ∑ j, p j ≤ ∑ j, q j) :
    ∀ x ∈ Dem M s p, ∀ y ∈ Dem M s q, totalRevenue p x ≤ totalRevenue q y := by
  intro x hx y hy
  cases s with
  | nonrivalrous =>
      have hx' : x ∈ DemNR M p := by simpa [Dem] using hx
      have hy' : y ∈ DemNR M q := by simpa [Dem] using hy
      calc
        totalRevenue p x = ∑ i, min (M.b i) (∑ j, p j) := by
          rw [nr_total_eq M p x hp hx']
        _ ≤ ∑ i, min (M.b i) (∑ j, q j) := by
          apply Finset.sum_le_sum
          intro i _
          exact min_le_min (le_refl _) hsum
        _ = totalRevenue q y := by
          rw [nr_total_eq M q y hq hy']
  | rivalrous =>
      have haffx : x ∈ AffR M p := by simpa [Dem, DemR, PO] using hx.1
      have haffy : y ∈ AffR M q := by simpa [Dem, DemR, PO] using hy.1
      have hpx : totalRevenue p x = min (∑ j, p j) M.totalBudget := by
        refine le_antisymm (r_rev_le M p x hp haffx) ?_
        exact r_rev_ge M p x hp hx
      have hqy : totalRevenue q y = min (∑ j, q j) M.totalBudget := by
        refine le_antisymm (r_rev_le M q y hq haffy) ?_
        exact r_rev_ge M q y hq hy
      rw [hpx, hqy]
      rw [min_comm, min_comm (∑ j, q j) M.totalBudget]
      exact min_le_min (le_refl _) hsum
