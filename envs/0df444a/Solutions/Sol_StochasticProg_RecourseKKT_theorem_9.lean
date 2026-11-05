-- Prove2me | solution 1 for StochasticProg.RecourseKKT.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T05:54:29.298958+00:00
-- url     : https://prove2.me/submissions/8018c062-69b2-4d0c-adc3-be4cf54bf5e8

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
import Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_IsOptimalDEP
import Definitions.Def_StochasticProg_RecourseKKT_HasFiniteOptimalValue
import Definitions.Def_StochasticProg_RecourseKKT_FiniteSecondMoments
import Definitions.Def_StochasticProg_RecourseKKT_RecourseNotNegInf
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential
import Definitions.Def_StochasticProg_RecourseKKT_IsPolyhedralSet

set_option autoImplicit false

namespace DJ

open Matrix

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩

end DJ


set_option autoImplicit false

open Matrix

namespace P2MKKT

variable {n : ℕ}

lemma cont_dot (a : Fin n → ℝ) : Continuous fun x : Fin n → ℝ => a ⬝ᵥ x := by
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

lemma dot_comb (v p q xs : Fin n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    v ⬝ᵥ (a • p + b • q - xs) = a * v ⬝ᵥ (p - xs) + b * v ⬝ᵥ (q - xs) := by
  simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
  linear_combination (v ⬝ᵥ xs) * hab

lemma lin_eq_sum (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    φ x = ∑ s, φ (Pi.single s 1) * x s := by
  have hx : x = ∑ s, x s • (Pi.single s (1:ℝ) : Fin n → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma lin_eq_dot (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    φ x = (fun s => φ (Pi.single s 1)) ⬝ᵥ x := by
  rw [lin_eq_sum]; rfl

lemma clm_prod_decomp (f : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin n → ℝ, ∃ β : ℝ, ∀ x r, f (x, r) = a ⬝ᵥ x + β * r := by
  refine ⟨fun i => f (Pi.single i 1, 0), f (0, 1), fun x r => ?_⟩
  have h1 : ((x, r) : (Fin n → ℝ) × ℝ) =
      (∑ i, x i • (((Pi.single i 1 : Fin n → ℝ), (0:ℝ)) : (Fin n → ℝ) × ℝ)) +
        r • (((0 : Fin n → ℝ), (1:ℝ)) : (Fin n → ℝ) × ℝ) := by
    refine Prod.ext ?_ ?_
    · funext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [h1, map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul, dotProduct]
  rw [mul_comm r]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma hb_sep (A B : Set ((Fin n → ℝ) × ℝ)) (hA : Convex ℝ A) (hB : Convex ℝ B) (hBo : IsOpen B)
    (hd : Disjoint B A) :
    ∃ a : Fin n → ℝ, ∃ β s : ℝ, (∀ x r, (x, r) ∈ B → a ⬝ᵥ x + β * r < s) ∧
      (∀ x r, (x, r) ∈ A → s ≤ a ⬝ᵥ x + β * r) := by
  obtain ⟨f, s, h1, h2⟩ := geometric_hahn_banach_open hB hBo hA hd
  obtain ⟨a, β, hf⟩ := clm_prod_decomp f
  refine ⟨a, β, s, fun x r hp => ?_, fun x r hp => ?_⟩
  · have := h1 (x, r) hp; rw [hf] at this; exact this
  · have := h2 (x, r) hp; rw [hf] at this; exact this

/-- Interior qualification: `N_{P ∩ K} ⊆ N_P + N_K` when `P` meets the interior of `K`. -/
lemma interior_rule (P K : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hK : Convex ℝ K)
    (x0 : Fin n → ℝ) (hx0P : x0 ∈ P) (hx0K : x0 ∈ interior K)
    (xs : Fin n → ℝ) (hxsP : xs ∈ P) (hxsK : xs ∈ K) (v : Fin n → ℝ)
    (hv : ∀ x ∈ P, x ∈ K → v ⬝ᵥ (x - xs) ≤ 0) :
    ∃ a : Fin n → ℝ, (∀ x ∈ K, a ⬝ᵥ (x - xs) ≤ 0) ∧ (∀ x ∈ P, (v - a) ⬝ᵥ (x - xs) ≤ 0) := by
  let A : Set ((Fin n → ℝ) × ℝ) := {p | p.1 ∈ P ∧ p.2 ≤ v ⬝ᵥ (p.1 - xs)}
  let B : Set ((Fin n → ℝ) × ℝ) := interior K ×ˢ Set.Ioi 0
  have hA : Convex ℝ A := by
    intro p hp q hq a b ha hb hab
    refine ⟨hP hp.1 hq.1 ha hb hab, ?_⟩
    show a * p.2 + b * q.2 ≤ v ⬝ᵥ (a • p.1 + b • q.1 - xs)
    rw [dot_comb v p.1 q.1 xs a b hab]
    have h1 := mul_le_mul_of_nonneg_left hp.2 ha
    have h2 := mul_le_mul_of_nonneg_left hq.2 hb
    linarith
  have hB : Convex ℝ B := (Convex.interior hK).prod (convex_Ioi 0)
  have hBo : IsOpen B := isOpen_interior.prod isOpen_Ioi
  have hd : Disjoint B A := by
    rw [Set.disjoint_left]
    rintro ⟨x, r⟩ ⟨hxK, hr⟩ ⟨hxP, hrv⟩
    have := hv x hxP (interior_subset hxK)
    simp only [Set.mem_Ioi] at hr
    simp only at hrv
    linarith
  obtain ⟨a, β, s, hBs, hAs⟩ := hb_sep A B hA hB hBo hd
  have hs1 : s ≤ a ⬝ᵥ xs := by
    have := hAs xs 0 ⟨hxsP, by simp⟩
    simpa using this
  have hβ : β < 0 := by
    have e1 := hBs x0 1 ⟨hx0K, by simp⟩
    have e2 := hAs x0 (-|v ⬝ᵥ (x0 - xs)| - 1) ⟨hx0P, by
      simp only
      linarith [neg_abs_le (v ⬝ᵥ (x0 - xs))]⟩
    by_contra hc
    push_neg at hc
    have : 0 ≤ β * (|v ⬝ᵥ (x0 - xs)| + 2) := mul_nonneg hc (by positivity)
    nlinarith
  have hint : ∀ x ∈ interior K, a ⬝ᵥ x ≤ s := by
    intro x hx
    by_contra hc
    push_neg at hc
    have hr : 0 < (a ⬝ᵥ x - s) / (-β) / 2 := by
      have : 0 < -β := by linarith
      positivity
    have := hBs x ((a ⬝ᵥ x - s) / (-β) / 2) ⟨hx, hr⟩
    have : β * ((a ⬝ᵥ x - s) / (-β) / 2) = -((a ⬝ᵥ x - s) / 2) := by
      calc β * ((a ⬝ᵥ x - s) / (-β) / 2) = (β / -β) * (a ⬝ᵥ x - s) / 2 := by ring
        _ = -((a ⬝ᵥ x - s) / 2) := by rw [div_neg_self hβ.ne]; ring
    linarith
  have hKs : ∀ x ∈ K, a ⬝ᵥ x ≤ s := by
    intro x hx
    have hne : (interior K).Nonempty := ⟨x0, hx0K⟩
    have hcl : x ∈ closure (interior K) := by
      rw [hK.closure_interior_eq_closure_of_nonempty_interior hne]
      exact subset_closure hx
    have hcs : closure (interior K) ⊆ {x | a ⬝ᵥ x ≤ s} :=
      closure_minimal hint (isClosed_le (cont_dot a) continuous_const)
    exact hcs hcl
  have hseq : s = a ⬝ᵥ xs := le_antisymm hs1 (hKs xs hxsK)
  have hγ : 0 < -β := by linarith
  refine ⟨(-β)⁻¹ • a, fun x hx => ?_, fun x hx => ?_⟩
  · rw [smul_dotProduct, smul_eq_mul, dotProduct_sub]
    have := hKs x hx
    have : a ⬝ᵥ x - a ⬝ᵥ xs ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hγ.le) this
  · have h := hAs x (v ⬝ᵥ (x - xs)) ⟨hx, le_rfl⟩
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    have h2 : (-β) * v ⬝ᵥ (x - xs) ≤ a ⬝ᵥ (x - xs) := by
      have e1 : a ⬝ᵥ (x - xs) = a ⬝ᵥ x - a ⬝ᵥ xs := dotProduct_sub _ _ _
      linarith
    have h3 : v ⬝ᵥ (x - xs) ≤ (-β)⁻¹ * a ⬝ᵥ (x - xs) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hγ]; linarith
    linarith

/-- Farkas with complementary slackness at a feasible point. -/
lemma farkas_active {τ : Type} [Fintype τ] (χ : τ → (Fin n → ℝ) →ₗ[ℝ] ℝ) (z : τ → ℝ)
    (xs : Fin n → ℝ) (hxs : ∀ t, χ t xs ≤ z t) (v : Fin n → ℝ)
    (hv : ∀ x, (∀ t, χ t x ≤ z t) → v ⬝ᵥ (x - xs) ≤ 0) :
    ∃ l : τ → ℝ, (∀ t, 0 ≤ l t) ∧ (∀ t, l t * (z t - χ t xs) = 0) ∧
      v = ∑ t, l t • (fun s => χ t (Pi.single s 1)) := by
  classical
  rcases DJ.fm_alt' (σ := Fin n) (ι := τ ⊕ Unit)
      (Sum.elim (fun t s => if χ t xs = z t then χ t (Pi.single s 1) else 0) (fun _ s => -v s))
      (Sum.elim (fun _ => 0) (fun _ => -1)) with ⟨d, hd⟩ | ⟨l, h0, h1, h2⟩
  · exfalso
    have hact : ∀ t, χ t xs = z t → χ t d ≤ 0 := by
      intro t ht
      have := hd (Sum.inl t)
      simp only [Sum.elim_inl, ht, if_true] at this
      rw [lin_eq_sum]; exact this
    have hvd : 1 ≤ v ⬝ᵥ d := by
      have := hd (Sum.inr ())
      simp only [Sum.elim_inr] at this
      have e : ∑ s, -v s * d s = -(v ⬝ᵥ d) := by
        simp [dotProduct, Finset.sum_neg_distrib]
      linarith
    have hev : ∀ t, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), χ t (xs + ε • d) ≤ z t := by
      intro t
      by_cases ht : χ t xs = z t
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [map_add, map_smul, smul_eq_mul, ht]
        have := hact t ht
        have : ε * χ t d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε) this
        linarith
      · have hlt : χ t xs < z t := lt_of_le_of_ne (hxs t) ht
        have hU : IsOpen {ε : ℝ | χ t xs + ε * χ t d < z t} :=
          isOpen_lt (continuous_const.add (continuous_id.mul continuous_const)) continuous_const
        have hm : {ε : ℝ | χ t xs + ε * χ t d < z t} ∈ nhds (0:ℝ) :=
          hU.mem_nhds (by simp only [Set.mem_setOf_eq, zero_mul, add_zero]; exact hlt)
        have hm' : ∀ᶠ ε in nhds (0:ℝ), χ t (xs + ε • d) ≤ z t := by
          filter_upwards [hm] with ε hε
          rw [map_add, map_smul, smul_eq_mul]
          exact le_of_lt hε
        exact nhdsWithin_le_nhds hm'
    have hall := (Filter.eventually_all.2 hev).and self_mem_nhdsWithin
    obtain ⟨ε, hε1, hε2⟩ := hall.exists
    have := hv (xs + ε • d) hε1
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at this
    have hε2' : (0:ℝ) < ε := hε2
    nlinarith
  · have hl0 : 0 < l (Sum.inr ()) := by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero,
        zero_add, Finset.univ_unique, Finset.sum_singleton] at h2
      linarith
    refine ⟨fun t => if χ t xs = z t then l (Sum.inl t) / l (Sum.inr ()) else 0,
      fun t => ?_, fun t => ?_, ?_⟩
    · simp only
      split_ifs
      · exact div_nonneg (h0 _) hl0.le
      · exact le_rfl
    · simp only
      split_ifs with h
      · rw [h, sub_self, mul_zero]
      · rw [zero_mul]
    · funext s
      have := h1 s
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton] at this
      rw [Finset.sum_apply]
      have e : ∑ t, (fun t => if χ t xs = z t then l (Sum.inl t) / l (Sum.inr ()) else 0) t •
          (fun s => χ t (Pi.single s 1)) s =
          (∑ t, l (Sum.inl t) * (if χ t xs = z t then χ t (Pi.single s 1) else 0)) / l (Sum.inr ()) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [smul_eq_mul]
        split_ifs <;> ring
      simp only [Pi.smul_apply] at e ⊢
      rw [e]
      field_simp
      linarith

/-- Normal cone of an intersection of two polyhedra splits. -/
lemma poly_rule {ι κ : Type} [Fintype ι] [Fintype κ] (φ : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (u : ι → ℝ)
    (ψ : κ → (Fin n → ℝ) →ₗ[ℝ] ℝ) (w : κ → ℝ) (xs : Fin n → ℝ)
    (h1 : ∀ i, φ i xs ≤ u i) (h2 : ∀ j, ψ j xs ≤ w j) (v : Fin n → ℝ)
    (hv : ∀ x, (∀ i, φ i x ≤ u i) → (∀ j, ψ j x ≤ w j) → v ⬝ᵥ (x - xs) ≤ 0) :
    ∃ v1 v2 : Fin n → ℝ, v = v1 + v2 ∧ (∀ x, (∀ i, φ i x ≤ u i) → v1 ⬝ᵥ (x - xs) ≤ 0) ∧
      (∀ x, (∀ j, ψ j x ≤ w j) → v2 ⬝ᵥ (x - xs) ≤ 0) := by
  classical
  obtain ⟨l, hl0, hcs, hsum⟩ := farkas_active (τ := ι ⊕ κ) (Sum.elim φ ψ) (Sum.elim u w) xs
    (fun t => by cases t with | inl i => exact h1 i | inr j => exact h2 j) v
    (fun x hx => hv x (fun i => hx (Sum.inl i)) (fun j => hx (Sum.inr j)))
  refine ⟨∑ i, l (Sum.inl i) • (fun s => φ i (Pi.single s 1)),
    ∑ j, l (Sum.inr j) • (fun s => ψ j (Pi.single s 1)), ?_, ?_, ?_⟩
  · rw [hsum, Fintype.sum_sum_type]; rfl
  · intro x hx
    rw [sum_dotProduct]
    have : ∀ i, (l (Sum.inl i) • (fun s => φ i (Pi.single s 1))) ⬝ᵥ (x - xs) ≤ 0 := by
      intro i
      rw [smul_dotProduct, smul_eq_mul, ← lin_eq_dot, map_sub]
      have hc := hcs (Sum.inl i)
      simp only [Sum.elim_inl] at hc
      have := hx i
      have hli := hl0 (Sum.inl i)
      nlinarith
    exact Finset.sum_nonpos fun i _ => this i
  · intro x hx
    rw [sum_dotProduct]
    have : ∀ j, (l (Sum.inr j) • (fun s => ψ j (Pi.single s 1))) ⬝ᵥ (x - xs) ≤ 0 := by
      intro j
      rw [smul_dotProduct, smul_eq_mul, ← lin_eq_dot, map_sub]
      have hc := hcs (Sum.inr j)
      simp only [Sum.elim_inr] at hc
      have := hx j
      have hli := hl0 (Sum.inr j)
      nlinarith
    exact Finset.sum_nonpos fun j _ => this j

/-- Sum rule for a finite continuous convex function plus the indicator of a convex set. -/
lemma sum_rule (g : (Fin n → ℝ) → ℝ) (hg : ConvexOn ℝ Set.univ g) (hgc : Continuous g)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (c xs : Fin n → ℝ) (hxs : xs ∈ C)
    (hopt : ∀ x ∈ C, c ⬝ᵥ xs + g xs ≤ c ⬝ᵥ x + g x) :
    ∃ ζ : Fin n → ℝ, (∀ x, g xs + ζ ⬝ᵥ (x - xs) ≤ g x) ∧ ∀ x ∈ C, 0 ≤ (c + ζ) ⬝ᵥ (x - xs) := by
  let φ : (Fin n → ℝ) → ℝ := fun x => c ⬝ᵥ x + g x - (c ⬝ᵥ xs + g xs)
  have hφc : Continuous φ := ((cont_dot c).add hgc).sub continuous_const
  let B : Set ((Fin n → ℝ) × ℝ) := {p | φ p.1 < p.2}
  let A : Set ((Fin n → ℝ) × ℝ) := C ×ˢ Set.Iic 0
  have hBo : IsOpen B := isOpen_lt (hφc.comp continuous_fst) continuous_snd
  have hB : Convex ℝ B := by
    rw [convex_iff_forall_pos]
    intro p hp q hq a b ha hb hab
    show c ⬝ᵥ (a • p.1 + b • q.1) + g (a • p.1 + b • q.1) - (c ⬝ᵥ xs + g xs) < a * p.2 + b * q.2
    have hgab := hg.2 (Set.mem_univ p.1) (Set.mem_univ q.1) ha.le hb.le hab
    simp only [smul_eq_mul] at hgab
    have hp' : c ⬝ᵥ p.1 + g p.1 - (c ⬝ᵥ xs + g xs) < p.2 := hp
    have hq' : c ⬝ᵥ q.1 + g q.1 - (c ⬝ᵥ xs + g xs) < q.2 := hq
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have e1 := mul_lt_mul_of_pos_left hp' ha
    have e2 := mul_lt_mul_of_pos_left hq' hb
    have e3 : c ⬝ᵥ xs + g xs = a * (c ⬝ᵥ xs + g xs) + b * (c ⬝ᵥ xs + g xs) := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hA : Convex ℝ A := hC.prod (convex_Iic 0)
  have hd : Disjoint B A := by
    rw [Set.disjoint_left]
    rintro ⟨x, r⟩ hB' ⟨hxC, hr⟩
    have h1 : φ x < r := hB'
    have h2 := hopt x hxC
    simp only [Set.mem_Iic] at hr
    have : 0 ≤ φ x := by simp only [φ]; linarith
    linarith
  obtain ⟨a, β, s, hBs, hAs⟩ := hb_sep A B hA hB hBo hd
  have hφxs : φ xs = 0 := by simp [φ]
  have hs1 : s ≤ a ⬝ᵥ xs := by
    have := hAs xs 0 ⟨hxs, by simp⟩
    simpa using this
  have hβ : β < 0 := by
    have := hBs xs 1 (by show φ xs < 1; rw [hφxs]; norm_num)
    linarith
  have hγ : 0 < -β := by linarith
  have hmain : ∀ x, a ⬝ᵥ x - s ≤ (-β) * φ x := by
    intro x
    by_contra hc
    push_neg at hc
    set δ := a ⬝ᵥ x - s - (-β) * φ x with hδ
    have hδp : 0 < δ := by linarith
    have hr : φ x < φ x + δ / (-β) / 2 := by
      have : 0 < δ / (-β) / 2 := by positivity
      linarith
    have := hBs x (φ x + δ / (-β) / 2) hr
    have e : β * (φ x + δ / (-β) / 2) = β * φ x - δ / 2 := by
      calc β * (φ x + δ / (-β) / 2) = β * φ x + (β / -β) * δ / 2 := by ring
        _ = β * φ x - δ / 2 := by rw [div_neg_self hβ.ne]; ring
    linarith
  have hs2 : a ⬝ᵥ xs ≤ s := by
    have := hmain xs
    rw [hφxs, mul_zero] at this
    linarith
  have hseq : s = a ⬝ᵥ xs := le_antisymm hs1 hs2
  refine ⟨(-β)⁻¹ • a - c, fun x => ?_, fun x hx => ?_⟩
  · have h := hmain x
    rw [hseq] at h
    have h' : (-β)⁻¹ * (a ⬝ᵥ x - a ⬝ᵥ xs) ≤ φ x := by
      rw [← div_eq_inv_mul, div_le_iff₀ hγ]; linarith
    simp only [φ] at h'
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_sub, dotProduct_sub]
    linarith
  · have h := hAs x 0 ⟨hx, by simp⟩
    rw [mul_zero, add_zero] at h
    rw [add_sub_cancel, smul_dotProduct, smul_eq_mul, dotProduct_sub]
    have : 0 ≤ a ⬝ᵥ x - a ⬝ᵥ xs := by linarith
    exact mul_nonneg (inv_nonneg.2 hγ.le) this

/-- Lipschitz convex extension (infimal convolution with `L ‖·‖`). -/
lemma lip_ext (K : Set (Fin n → ℝ)) (hKne : K.Nonempty) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ K f) (L : NNReal) (hL : LipschitzOnWith L f K) :
    ∃ g : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ g ∧ Continuous g ∧ ∀ x ∈ K, g x = f x := by
  obtain ⟨y0, hy0⟩ := hKne
  have hd := lipschitzOnWith_iff_dist_le_mul.1 hL
  have hK : Convex ℝ K := hf.1
  have : Nonempty K := ⟨⟨y0, hy0⟩⟩
  have hL0 : (0:ℝ) ≤ L := L.2
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℝ) → K → ℝ, F = fun (x : Fin n → ℝ) (y : K) => f y + L * dist x (y : Fin n → ℝ) := ⟨_, rfl⟩
  have hbdd : ∀ x, BddBelow (Set.range (F x)) := by
    intro x
    refine ⟨f y0 - L * dist x y0, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := hd y y.2 y0 hy0
    have h2 : dist (y:Fin n → ℝ) y0 ≤ dist x y + dist x y0 := by
      have := dist_triangle (y:Fin n → ℝ) x y0
      rw [dist_comm (y:Fin n → ℝ) x] at this
      exact this
    have h3 : f y0 - f y ≤ dist (f y) (f y0) := by
      rw [Real.dist_eq, abs_sub_comm]; exact le_abs_self _
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    rw [hF]
    show f y0 - L * dist x y0 ≤ f y + L * dist x y
    linarith
  obtain ⟨g, hg⟩ : ∃ g : (Fin n → ℝ) → ℝ, g = fun x => ⨅ y, F x y := ⟨_, rfl⟩
  have hgle : ∀ x (y : K), g x ≤ f y + L * dist x y := by
    intro x y
    have := ciInf_le (hbdd x) y
    rw [hg]; rw [hF] at this ⊢; exact this
  have hgge : ∀ (x : Fin n → ℝ) (b : ℝ), (∀ y : K, b ≤ f y + L * dist x (y : Fin n → ℝ)) → b ≤ g x := by
    intro x b h
    rw [hg]
    exact le_ciInf (fun y => by rw [hF]; exact h y)
  have hlip : ∀ x x', g x ≤ g x' + L * dist x x' := by
    intro x x'
    have : g x - L * dist x x' ≤ g x' := by
      apply hgge
      intro y
      have h1 := hgle x y
      have h2 : dist x y ≤ dist x x' + dist x' y := dist_triangle _ _ _
      have h4 := mul_le_mul_of_nonneg_left h2 hL0
      linarith
    linarith
  refine ⟨g, ⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x1 _ x2 _ a b ha hb hab
    simp only [smul_eq_mul]
    by_contra hc
    push_neg at hc
    set ε := g (a • x1 + b • x2) - (a * g x1 + b * g x2) with hε
    have hεp : 0 < ε := by linarith
    have eg : ∀ x, (⨅ y, F x y) = g x := fun x => by rw [hg]
    obtain ⟨y1, hy1⟩ := exists_lt_of_ciInf_lt (f := F x1)
      (show (⨅ y, F x1 y) < g x1 + ε / 2 by rw [eg]; linarith)
    obtain ⟨y2, hy2⟩ := exists_lt_of_ciInf_lt (f := F x2)
      (show (⨅ y, F x2 y) < g x2 + ε / 2 by rw [eg]; linarith)
    have hmem : a • (y1 : Fin n → ℝ) + b • (y2 : Fin n → ℝ) ∈ K := hK y1.2 y2.2 ha hb hab
    have h1 : g (a • x1 + b • x2) ≤ f (a • (y1 : Fin n → ℝ) + b • (y2 : Fin n → ℝ)) +
        L * dist (a • x1 + b • x2) (a • (y1 : Fin n → ℝ) + b • (y2 : Fin n → ℝ)) :=
      hgle (a • x1 + b • x2) ⟨_, hmem⟩
    have h2 := hf.2 y1.2 y2.2 ha hb hab
    simp only [smul_eq_mul] at h2
    have h3 : dist (a • x1 + b • x2) (a • (y1 : Fin n → ℝ) + b • (y2 : Fin n → ℝ)) ≤
        a * dist x1 y1 + b * dist x2 y2 := by
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      have : a • x1 + b • x2 - (a • (y1 : Fin n → ℝ) + b • (y2 : Fin n → ℝ)) =
          a • (x1 - y1) + b • (x2 - y2) := by
        rw [smul_sub, smul_sub]; abel
      rw [this]
      calc ‖a • (x1 - y1) + b • (x2 - (y2 : Fin n → ℝ))‖
          ≤ ‖a • (x1 - y1)‖ + ‖b • (x2 - (y2 : Fin n → ℝ))‖ := norm_add_le _ _
        _ = a * ‖x1 - y1‖ + b * ‖x2 - y2‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hy1' : f y1 + L * dist x1 y1 < g x1 + ε / 2 := by rw [hF] at hy1; exact hy1
    have hy2' : f y2 + L * dist x2 y2 < g x2 + ε / 2 := by rw [hF] at hy2; exact hy2
    have e1 := mul_le_mul_of_nonneg_left hy1'.le ha
    have e2 := mul_le_mul_of_nonneg_left hy2'.le hb
    have e3 := mul_le_mul_of_nonneg_left h3 hL0
    have e4 : a * (ε / 2) + b * (ε / 2) = ε / 2 := by rw [← add_mul, hab, one_mul]
    nlinarith
  · refine (LipschitzWith.of_dist_le_mul (K := L) fun x x' => ?_).continuous
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · have := hlip x x'; linarith
    · have := hlip x' x; rw [dist_comm] at this; linarith
  · intro x hx
    apply le_antisymm
    · have := hgle x ⟨x, hx⟩
      simpa using this
    · apply hgge
      intro y
      have h1 := hd x hx y y.2
      have h3 : f x - f y ≤ dist (f x) (f y) := by
        rw [Real.dist_eq]; exact le_abs_self _
      linarith

/-- Abstract KKT: a convex Lipschitz `f` on `K2`, minimiser of `c·x + f` over `K1 ∩ K2`,
and a normal-cone splitting at `xs`. -/
theorem abstract_kkt (K1 K2 : Set (Fin n → ℝ)) (hK1 : Convex ℝ K1) (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ K2 f) (L : NNReal) (hL : LipschitzOnWith L f K2) (c xs : Fin n → ℝ)
    (hxs1 : xs ∈ K1) (hxs2 : xs ∈ K2)
    (hopt : ∀ x ∈ K1, x ∈ K2 → c ⬝ᵥ xs + f xs ≤ c ⬝ᵥ x + f x)
    (hsplit : ∀ v : Fin n → ℝ, (∀ x ∈ K1, x ∈ K2 → v ⬝ᵥ (x - xs) ≤ 0) →
      ∃ v1 v2 : Fin n → ℝ, v = v1 + v2 ∧ (∀ x ∈ K1, v1 ⬝ᵥ (x - xs) ≤ 0) ∧
        (∀ x ∈ K2, v2 ⬝ᵥ (x - xs) ≤ 0)) :
    ∃ ζ : Fin n → ℝ, (∀ w ∈ K2, f xs + ζ ⬝ᵥ (w - xs) ≤ f w) ∧
      ∀ x ∈ K1, 0 ≤ (c + ζ) ⬝ᵥ (x - xs) := by
  obtain ⟨g, hgc, hgcont, hgf⟩ := lip_ext K2 ⟨xs, hxs2⟩ f hf L hL
  obtain ⟨ζ0, hζ0, hC⟩ := sum_rule g hgc hgcont (K1 ∩ K2) (hK1.inter hf.1) c xs ⟨hxs1, hxs2⟩
    (fun x hx => by rw [hgf xs hxs2, hgf x hx.2]; exact hopt x hx.1 hx.2)
  obtain ⟨v1, v2, hv, hv1, hv2⟩ := hsplit (-(c + ζ0)) (fun x h1 h2 => by
    have := hC x ⟨h1, h2⟩
    rw [neg_dotProduct]; linarith)
  refine ⟨ζ0 + v2, fun w hw => ?_, fun x hx => ?_⟩
  · have h1 := hζ0 w
    have h2 := hv2 w hw
    rw [hgf xs hxs2, hgf w hw] at h1
    rw [add_dotProduct]
    linarith
  · have h1 := hv1 x hx
    have e : c + (ζ0 + v2) = -v1 := by
      have : v1 = -(c + ζ0) - v2 := by rw [hv]; abel
      rw [this]; abel
    rw [e, neg_dotProduct]
    linarith


lemma K1_poly {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∃ (φ : (Fin m ⊕ (Fin m ⊕ Fin n)) → (Fin n → ℝ) →ₗ[ℝ] ℝ) (u : Fin m ⊕ (Fin m ⊕ Fin n) → ℝ),
      ∀ x, (A *ᵥ x = b ∧ 0 ≤ x) ↔ ∀ i, φ i x ≤ u i := by
  refine ⟨Sum.elim (fun r => LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) r ∘ₗ Matrix.toLin' A)
    (Sum.elim (fun r => -(LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) r ∘ₗ Matrix.toLin' A))
      (fun s => -(LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) s))),
    Sum.elim b (Sum.elim (-b) 0), fun x => ?_⟩
  constructor
  · rintro ⟨h1, h2⟩ i
    rcases i with r | r | s
    · simp [Matrix.toLin'_apply, h1]
    · simp [Matrix.toLin'_apply, h1]
    · simp only [Sum.elim_inr, LinearMap.neg_apply, LinearMap.coe_proj, Function.eval,
        Pi.zero_apply, neg_nonpos]
      exact h2 s
  · intro h
    refine ⟨funext fun r => le_antisymm ?_ ?_, Pi.le_def.2 fun s => ?_⟩
    · have := h (Sum.inl r)
      simpa [Matrix.toLin'_apply] using this
    · have := h (Sum.inr (Sum.inl r))
      simp [Matrix.toLin'_apply] at this
      linarith
    · have := h (Sum.inr (Sum.inr s))
      simp only [Sum.elim_inr, LinearMap.neg_apply, LinearMap.coe_proj, Function.eval,
        Pi.zero_apply, neg_nonpos] at this
      exact this

lemma K1_convex {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ {x : Fin n → ℝ | A *ᵥ x = b ∧ 0 ≤ x} := by
  intro x hx y hy a c ha hc hac
  refine ⟨?_, add_nonneg (smul_nonneg ha hx.2) (smul_nonneg hc hy.2)⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx.1, hy.1, ← add_smul, hac,
    one_smul]

/-- Splitting when `K₂` is a convex polyhedron. -/
lemma split_poly {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (K2 : Set (Fin n → ℝ))
    (hK2 : ∃ (k : ℕ) (ψ : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (w : Fin k → ℝ), K2 = {x | ∀ i, ψ i x ≤ w i})
    (xs : Fin n → ℝ) (hxs1 : A *ᵥ xs = b ∧ 0 ≤ xs) (hxs2 : xs ∈ K2) (v : Fin n → ℝ)
    (hv : ∀ x ∈ {x : Fin n → ℝ | A *ᵥ x = b ∧ 0 ≤ x}, x ∈ K2 → v ⬝ᵥ (x - xs) ≤ 0) :
    ∃ v1 v2 : Fin n → ℝ, v = v1 + v2 ∧
      (∀ x ∈ {x : Fin n → ℝ | A *ᵥ x = b ∧ 0 ≤ x}, v1 ⬝ᵥ (x - xs) ≤ 0) ∧
      (∀ x ∈ K2, v2 ⬝ᵥ (x - xs) ≤ 0) := by
  obtain ⟨k, ψ, w, rfl⟩ := hK2
  obtain ⟨φ, u, hφ⟩ := K1_poly A b
  obtain ⟨v1, v2, hv12, h1, h2⟩ := poly_rule φ u ψ w xs ((hφ xs).1 hxs1) hxs2 v
    (fun x hx1 hx2 => hv x ((hφ x).2 hx1) hx2)
  exact ⟨v1, v2, hv12, fun x hx => h1 x ((hφ x).1 hx), fun x hx => h2 x hx⟩

/-- Splitting when `K₁ ⊆ K₂`. -/
lemma split_sub (K1 K2 : Set (Fin n → ℝ)) (hsub : K1 ⊆ K2) (xs v : Fin n → ℝ)
    (hv : ∀ x ∈ K1, x ∈ K2 → v ⬝ᵥ (x - xs) ≤ 0) :
    ∃ v1 v2 : Fin n → ℝ, v = v1 + v2 ∧ (∀ x ∈ K1, v1 ⬝ᵥ (x - xs) ≤ 0) ∧
      (∀ x ∈ K2, v2 ⬝ᵥ (x - xs) ≤ 0) :=
  ⟨v, 0, (add_zero v).symm, fun x hx => hv x hx (hsub hx), fun x _ => by simp⟩

/-- Splitting when `K₁` meets the relative interior of `K₂`. -/
lemma split_ri {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (K2 : Set (Fin n → ℝ))
    (hK2 : Convex ℝ K2) (x0 : Fin n → ℝ) (hx01 : A *ᵥ x0 = b ∧ 0 ≤ x0)
    (hx0r : x0 ∈ intrinsicInterior ℝ K2)
    (xs : Fin n → ℝ) (hxs1 : A *ᵥ xs = b ∧ 0 ≤ xs) (hxs2 : xs ∈ K2) (v : Fin n → ℝ)
    (hv : ∀ x ∈ {x : Fin n → ℝ | A *ᵥ x = b ∧ 0 ≤ x}, x ∈ K2 → v ⬝ᵥ (x - xs) ≤ 0) :
    ∃ v1 v2 : Fin n → ℝ, v = v1 + v2 ∧
      (∀ x ∈ {x : Fin n → ℝ | A *ᵥ x = b ∧ 0 ≤ x}, v1 ⬝ᵥ (x - xs) ≤ 0) ∧
      (∀ x ∈ K2, v2 ⬝ᵥ (x - xs) ≤ 0) := by
  classical
  set S : AffineSubspace ℝ (Fin n → ℝ) := affineSpan ℝ K2 with hSdef
  set V : Submodule ℝ (Fin n → ℝ) := S.direction with hVdef
  have hxsS : xs ∈ S := mem_affineSpan ℝ hxs2
  have hK2S : ∀ x ∈ K2, x ∈ S := fun x hx => mem_affineSpan ℝ hx
  obtain ⟨y, hy, hyx⟩ := mem_intrinsicInterior.1 hx0r
  have hx0S : x0 ∈ S := by rw [← hyx]; exact y.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hballK : ∀ z ∈ S, dist z x0 < ε → z ∈ K2 := by
    intro z hz hd
    have : (⟨z, hz⟩ : S) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, hyx]; exact hd
    have h := hball this
    exact (interior_subset h : (⟨z, hz⟩ : S) ∈ Subtype.val ⁻¹' K2)
  obtain ⟨W, hVW⟩ := Submodule.exists_isCompl V
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let pV : (Fin n → ℝ) →ₗ[ℝ] V := LinearMap.fst ℝ V W ∘ₗ e.symm.toLinearMap
  let pW : (Fin n → ℝ) →ₗ[ℝ] W := LinearMap.snd ℝ V W ∘ₗ e.symm.toLinearMap
  have hdec : ∀ x, ((pV x : V) : Fin n → ℝ) + ((pW x : W) : Fin n → ℝ) = x := by
    intro x
    have := e.apply_symm_apply x
    rw [Submodule.coe_prodEquivOfIsCompl'] at this
    exact this
  have hpVc : Continuous fun x => ((pV x : V) : Fin n → ℝ) :=
    continuous_subtype_val.comp (LinearMap.continuous_of_finiteDimensional pV)
  -- the thickened set
  let K2' : Set (Fin n → ℝ) := {x | ∃ w ∈ W, x - w ∈ K2}
  have hK2'c : Convex ℝ K2' := by
    rintro x ⟨w1, hw1, h1⟩ x' ⟨w2, hw2, h2⟩ a c ha hc hac
    refine ⟨a • w1 + c • w2, W.add_mem (W.smul_mem a hw1) (W.smul_mem c hw2), ?_⟩
    have := hK2 h1 h2 ha hc hac
    have e1 : a • x + c • x' - (a • w1 + c • w2) = a • (x - w1) + c • (x' - w2) := by
      rw [smul_sub, smul_sub]; abel
    rw [e1]; exact this
  have hK2sub : ∀ x ∈ K2, x ∈ K2' := fun x hx => ⟨0, W.zero_mem, by simpa using hx⟩
  have hx0int : x0 ∈ interior K2' := by
    rw [mem_interior_iff_mem_nhds]
    have hρc : Continuous fun x => x0 + ((pV (x - x0) : V) : Fin n → ℝ) :=
      continuous_const.add (hpVc.comp (continuous_id.sub continuous_const))
    have hρ0 : (fun x => x0 + ((pV (x - x0) : V) : Fin n → ℝ)) x0 = x0 := by simp
    have hev : ∀ᶠ x in nhds x0, dist (x0 + ((pV (x - x0) : V) : Fin n → ℝ)) x0 < ε := by
      have ht := hρc.tendsto x0
      have h0 : x0 + ((pV (x0 - x0) : V) : Fin n → ℝ) = x0 := by simp
      rw [h0] at ht
      exact ht (Metric.ball_mem_nhds x0 hε)
    filter_upwards [hev] with x hx
    refine ⟨((pW (x - x0) : W) : Fin n → ℝ), (pW (x - x0)).2, ?_⟩
    have hS' : x0 + ((pV (x - x0) : V) : Fin n → ℝ) ∈ S := by
      have := AffineSubspace.vadd_mem_of_mem_direction (pV (x - x0)).2 hx0S
      rwa [vadd_eq_add, add_comm] at this
    have hk := hballK _ hS' hx
    have e1 : x - ((pW (x - x0) : W) : Fin n → ℝ) = x0 + ((pV (x - x0) : V) : Fin n → ℝ) := by
      have h := hdec (x - x0)
      calc x - ((pW (x - x0) : W) : Fin n → ℝ)
          = (x - x0) - ((pW (x - x0) : W) : Fin n → ℝ) + x0 := by abel
        _ = (((pV (x - x0) : V) : Fin n → ℝ) + ((pW (x - x0) : W) : Fin n → ℝ)) -
              ((pW (x - x0) : W) : Fin n → ℝ) + x0 := by rw [h]
        _ = x0 + ((pV (x - x0) : V) : Fin n → ℝ) := by abel
    rw [e1]; exact hk
  -- P = K1 ∩ S
  let P : Set (Fin n → ℝ) := {x | A *ᵥ x = b ∧ 0 ≤ x} ∩ (S : Set (Fin n → ℝ))
  have hPc : Convex ℝ P := (K1_convex A b).inter S.convex
  have hvP : ∀ x ∈ P, x ∈ K2' → v ⬝ᵥ (x - xs) ≤ 0 := by
    rintro x ⟨hx1, hxS⟩ ⟨w, hwW, hwK⟩
    have hwV : w ∈ V := by
      have := AffineSubspace.vsub_mem_direction hxS (hK2S _ hwK)
      rwa [vsub_eq_sub, sub_sub_cancel] at this
    have hw0 : w = 0 := (Submodule.disjoint_def.1 hVW.1) w hwV hwW
    rw [hw0, sub_zero] at hwK
    exact hv x hx1 hwK
  obtain ⟨a, ha2, haP⟩ := interior_rule P K2' hPc hK2'c x0 ⟨hx01, hx0S⟩ hx0int xs ⟨hxs1, hxsS⟩
    (hK2sub xs hxs2) v hvP
  -- S as a polyhedron
  let bQ := Module.finBasis ℝ ((Fin n → ℝ) ⧸ V)
  let ψ0 : Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ V)) → (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    fun j => bQ.coord j ∘ₗ V.mkQ
  have hψV : ∀ x, (∀ j, ψ0 j x = 0) ↔ x ∈ V := by
    intro x
    simp only [ψ0, LinearMap.coe_comp, Function.comp_apply]
    rw [bQ.forall_coord_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  let ψ : (Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ V)) ⊕ Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ V))) →
      (Fin n → ℝ) →ₗ[ℝ] ℝ := Sum.elim ψ0 (fun j => -ψ0 j)
  let w : (Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ V)) ⊕ Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ V))) → ℝ :=
    Sum.elim (fun j => ψ0 j xs) (fun j => -ψ0 j xs)
  have hψS : ∀ x, (∀ j, ψ j x ≤ w j) ↔ x ∈ S := by
    intro x
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hxsS x, vsub_eq_sub, ← hψV]
    constructor
    · intro h j
      have h1 := h (Sum.inl j)
      have h2 := h (Sum.inr j)
      simp only [ψ, w, Sum.elim_inl, Sum.elim_inr, LinearMap.neg_apply] at h1 h2
      rw [map_sub]; linarith
    · intro h j
      rcases j with j | j
      · have := h j; rw [map_sub] at this
        simp only [ψ, w, Sum.elim_inl]; linarith
      · have := h j; rw [map_sub] at this
        simp only [ψ, w, Sum.elim_inr, LinearMap.neg_apply]; linarith
  obtain ⟨φ, u, hφ⟩ := K1_poly A b
  obtain ⟨v1, v2, hv12, h1, h2⟩ := poly_rule φ u ψ w xs ((hφ xs).1 hxs1) ((hψS xs).2 hxsS)
    (v - a) (fun x hx1 hx2 => haP x ⟨(hφ x).2 hx1, (hψS x).1 hx2⟩)
  refine ⟨v1, v2 + a, ?_, fun x hx => h1 x ((hφ x).1 hx), fun x hx => ?_⟩
  · rw [← add_assoc, ← hv12]; abel
  · rw [add_dotProduct]
    have e1 := h2 x ((hψS x).2 (hK2S x hx))
    have e2 := ha2 x (hK2sub x hx)
    linarith

end P2MKKT

open Matrix StochasticProg.RecourseKKT in
theorem nc_K1 {n1 m1 : ℕ} (A : Matrix (Fin m1) (Fin n1) ℝ)
    (b : Fin m1 → ℝ) (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet A b) :
    {η : Fin n1 → ℝ | ∀ x ∈ firstStageSet A b, 0 ≤ η ⬝ᵥ (x - xs)} =
      {η | ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
        η = Aᵀ *ᵥ lam + mu} := by
  ext η
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hη
    rcases DJ.fm_alt' (σ := Fin m1) (ι := Fin n1 ⊕ Fin n1)
      (Sum.elim (fun j k => A k j) (fun j k => -(xs j * A k j)))
      (Sum.elim (fun j => η j) (fun j => -(xs j * η j))) with ⟨lam, hlam⟩ | ⟨l, hl0, hl1, hl2⟩
    · have hT : ∀ j, (Aᵀ *ᵥ lam) j = ∑ k, A k j * lam k := by
        intro j; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      have h1 : ∀ j, (Aᵀ *ᵥ lam) j ≤ η j := fun j => by
        rw [hT]; simpa using hlam (Sum.inl j)
      have h2 : ∀ j, xs j * η j ≤ xs j * (Aᵀ *ᵥ lam) j := fun j => by
        have := hlam (Sum.inr j)
        simp only [Sum.elim_inr] at this
        rw [hT, Finset.mul_sum]
        have e : ∑ k, -(xs j * A k j) * lam k = -∑ k, xs j * (A k j * lam k) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
        linarith
      refine ⟨lam, η - Aᵀ *ᵥ lam, fun j => ?_, ?_, by simp⟩
      · simp only [Pi.zero_apply, Pi.sub_apply]; linarith [h1 j]
      · simp only [dotProduct]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have hx := hxs.2 j
        simp only [Pi.zero_apply] at hx
        simp only [Pi.sub_apply]
        exact le_antisymm (by nlinarith [h2 j]) (mul_nonneg (by linarith [h1 j]) hx)
    · exfalso
      let d : Fin n1 → ℝ := fun j => l (Sum.inl j) - l (Sum.inr j) * xs j
      have hAd : A *ᵥ d = 0 := by
        funext k
        have := hl1 k
        rw [Fintype.sum_sum_type] at this
        simp only [Sum.elim_inl, Sum.elim_inr] at this
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, d]
        rw [← this, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hηd : η ⬝ᵥ d < 0 := by
        rw [Fintype.sum_sum_type] at hl2
        simp only [Sum.elim_inl, Sum.elim_inr] at hl2
        have e : η ⬝ᵥ d = ∑ j, l (Sum.inl j) * η j + ∑ j, l (Sum.inr j) * -(xs j * η j) := by
          simp only [dotProduct, d]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [e]; exact hl2
      have hS0 : 0 ≤ ∑ j, l (Sum.inr j) := Finset.sum_nonneg (fun j _ => hl0 (Sum.inr j))
      set S : ℝ := 1 + ∑ j, l (Sum.inr j) with hS
      have hSpos : 0 < S := by linarith
      set t : ℝ := 1 / S with ht
      have htpos : 0 < t := by positivity
      have hle : ∀ j, t * l (Sum.inr j) ≤ 1 := by
        intro j
        have hj : l (Sum.inr j) ≤ ∑ j, l (Sum.inr j) :=
          Finset.single_le_sum (f := fun j => l (Sum.inr j)) (fun j _ => hl0 (Sum.inr j))
            (Finset.mem_univ j)
        rw [ht, div_mul_eq_mul_div, one_mul, div_le_one hSpos]
        linarith
      have hxmem : xs + t • d ∈ firstStageSet A b := by
        refine ⟨?_, fun j => ?_⟩
        · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAd, smul_zero, add_zero]; exact hxs.1
        · have hx := hxs.2 j
          simp only [Pi.zero_apply] at hx
          simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, d]
          have e : xs j + t * (l (Sum.inl j) - l (Sum.inr j) * xs j)
              = xs j * (1 - t * l (Sum.inr j)) + t * l (Sum.inl j) := by ring
          rw [e]
          exact add_nonneg (mul_nonneg hx (sub_nonneg.mpr (hle j)))
            (mul_nonneg htpos.le (hl0 (Sum.inl j)))
      have h := hη _ hxmem
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at h
      have := mul_neg_of_pos_of_neg htpos hηd
      linarith
  · rintro ⟨lam, mu, hmu, hmux, rfl⟩ x hx
    have hAx : A *ᵥ (x - xs) = 0 := by rw [Matrix.mulVec_sub, hx.1, hxs.1, sub_self]
    have hlam : (Aᵀ *ᵥ lam) ⬝ᵥ (x - xs) = 0 := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAx, dotProduct_zero]
    rw [add_dotProduct, hlam, dotProduct_sub, hmux, zero_add, sub_zero]
    exact dotProduct_nonneg_of_nonneg hmu hx.2


open MeasureTheory Matrix StochasticProg.RecourseKKT in
theorem suff9 {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b)
    (hkkt : ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
          -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) :
    IsOptimalDEP P pb xs := by
  obtain ⟨lam, mu, hmu, hmux, r, hr, hsub⟩ := hkkt
  refine ⟨hxs, fun x hx => ?_⟩
  have key := hsub x
  have hAx : pb.A *ᵥ (x - xs) = 0 := by rw [Matrix.mulVec_sub, hx.1, hxs.1, sub_self]
  have hlam : (pb.Aᵀ *ᵥ lam) ⬝ᵥ (x - xs) = 0 := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAx, dotProduct_zero]
  have hmu0 : 0 ≤ mu ⬝ᵥ x := dotProduct_nonneg_of_nonneg hmu hx.2
  have hineq : pb.c ⬝ᵥ xs - pb.c ⬝ᵥ x ≤ (-pb.c + pb.Aᵀ *ᵥ lam + mu) ⬝ᵥ (x - xs) := by
    rw [add_dotProduct, add_dotProduct, hlam]
    simp only [dotProduct_sub, neg_dotProduct, hmux]
    linarith
  unfold depObjective
  rw [hr]
  calc ((pb.c ⬝ᵥ xs : ℝ) : EReal) + (r : EReal)
      = ((pb.c ⬝ᵥ x : ℝ) : EReal) + ((r + (pb.c ⬝ᵥ xs - pb.c ⬝ᵥ x) : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring
    _ ≤ ((pb.c ⬝ᵥ x : ℝ) : EReal) + ((r + (-pb.c + pb.Aᵀ *ᵥ lam + mu) ⬝ᵥ (x - xs) : ℝ) : EReal) := by
        exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
    _ ≤ ((pb.c ⬝ᵥ x : ℝ) : EReal) + expectedRecourse P pb x := add_le_add le_rfl key




set_option autoImplicit false

open Matrix


namespace P2MLP

open Matrix

variable {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)

/-- LP value `inf {q·y | y ≥ 0, W y = d}` in `EReal`. -/
noncomputable def lpv (q : Fin n → ℝ) (d : Fin m → ℝ) : EReal :=
  sInf ((fun y : Fin n → ℝ => ((q ⬝ᵥ y : ℝ) : EReal)) '' {y | 0 ≤ y ∧ W *ᵥ y = d})

lemma weak {q : Fin n → ℝ} {d : Fin m → ℝ} {π : Fin m → ℝ} {y : Fin n → ℝ}
    (hπ : π ᵥ* W ≤ q) (hy0 : 0 ≤ y) (hy : W *ᵥ y = d) : π ⬝ᵥ d ≤ q ⬝ᵥ y := by
  rw [← hy, dotProduct_mulVec]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hπ j) (hy0 j)

lemma strong {q : Fin n → ℝ} {d : Fin m → ℝ} {π0 : Fin m → ℝ} {y0 : Fin n → ℝ}
    (hπ0 : π0 ᵥ* W ≤ q) (hy00 : 0 ≤ y0) (hy0 : W *ᵥ y0 = d) :
    ∃ y π, 0 ≤ y ∧ W *ᵥ y = d ∧ π ᵥ* W ≤ q ∧ q ⬝ᵥ y ≤ π ⬝ᵥ d := by
  classical
  rcases DJ.fm_alt' (σ := Fin n ⊕ Fin m) (ι := Fin m ⊕ (Fin m ⊕ (Fin n ⊕ (Fin n ⊕ Unit))))
      (Sum.elim (fun i => Sum.elim (fun j => W i j) 0)
        (Sum.elim (fun i => Sum.elim (fun j => -W i j) 0)
          (Sum.elim (fun j' => Sum.elim (fun j => if j = j' then -1 else 0) 0)
            (Sum.elim (fun j' => Sum.elim 0 (fun i => W i j'))
              (fun _ => Sum.elim q (fun i => -d i))))))
      (Sum.elim d (Sum.elim (fun i => -d i) (Sum.elim 0 (Sum.elim q 0)))) with
    ⟨z, hz⟩ | ⟨l, h0, h1, h2⟩
  · refine ⟨fun j => z (Sum.inl j), fun i => z (Sum.inr i), ?_, ?_, ?_, ?_⟩
    · intro j
      have := hz (Sum.inr (Sum.inr (Sum.inl j)))
      simp [Fintype.sum_sum_type] at this
      simp only [Pi.zero_apply]
      linarith
    · funext i
      have e1 := hz (Sum.inl i)
      have e2 := hz (Sum.inr (Sum.inl i))
      simp [Fintype.sum_sum_type] at e1 e2
      simp only [Matrix.mulVec, dotProduct]
      linarith
    · intro j
      have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (W i j))]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (d i))]
      linarith
  · exfalso
    let u : Fin m → ℝ := fun i => l (Sum.inl i) - l (Sum.inr (Sum.inl i))
    let γ : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inl j)))
    let δ : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
    let τ : ℝ := l (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
    have hγ : ∀ j, 0 ≤ γ j := fun j => h0 _
    have hδ : 0 ≤ δ := fun j => h0 _
    have hτ : 0 ≤ τ := h0 _
    have E1 : ∀ j, (u ᵥ* W) j + τ * q j = γ j := by
      intro j
      have := h1 (Sum.inl j)
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, u, sub_mul, Finset.sum_sub_distrib, γ, τ]
      linarith
    have E2 : W *ᵥ δ = τ • d := by
      funext i
      have := h1 (Sum.inr i)
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, δ, τ, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (W i j) (l (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))))]
      linarith
    have R : u ⬝ᵥ d + δ ⬝ᵥ q < 0 := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, u, δ, sub_mul, Finset.sum_sub_distrib]
      linarith
    -- τ * (u·d + δ·q) ≥ 0
    have K1 : τ * (δ ⬝ᵥ q) ≥ -(τ * (u ⬝ᵥ d)) := by
      have hq : τ • q = γ - u ᵥ* W := by
        funext j; simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]; linarith [E1 j]
      have e1 : τ * (δ ⬝ᵥ q) = δ ⬝ᵥ γ - δ ⬝ᵥ (u ᵥ* W) := by
        rw [← dotProduct_sub, ← hq, dotProduct_smul, smul_eq_mul]
      have e2 : δ ⬝ᵥ (u ᵥ* W) = τ * (u ⬝ᵥ d) := by
        rw [dotProduct_comm, ← dotProduct_mulVec, E2, dotProduct_smul, smul_eq_mul]
      have e3 : 0 ≤ δ ⬝ᵥ γ := dotProduct_nonneg_of_nonneg hδ (fun j => hγ j)
      linarith
    rcases hτ.lt_or_eq with hpos | hzero
    · have : 0 ≤ τ * (u ⬝ᵥ d + δ ⬝ᵥ q) := by rw [mul_add]; linarith
      have := (mul_nonneg_iff_of_pos_left hpos).1 this
      linarith
    · have hWd : W *ᵥ δ = 0 := by rw [E2, ← hzero, zero_smul]
      have hu : u ᵥ* W = γ := by
        funext j; have := E1 j; rw [← hzero, zero_mul, add_zero] at this; exact this
      have e1 : 0 ≤ u ⬝ᵥ d := by
        rw [← hy0, dotProduct_mulVec, hu]
        exact dotProduct_nonneg_of_nonneg (fun j => hγ j) hy00
      have e2 : 0 ≤ δ ⬝ᵥ q := by
        have := weak W hπ0 hδ hWd
        rw [dotProduct_zero, dotProduct_comm] at this
        exact this
      linarith

lemma unbdd {q : Fin n → ℝ} {d : Fin m → ℝ} {y0 : Fin n → ℝ} (hy00 : 0 ≤ y0) (hy0 : W *ᵥ y0 = d)
    (hnd : ¬ ∃ π : Fin m → ℝ, π ᵥ* W ≤ q) (M : ℝ) :
    ∃ y, 0 ≤ y ∧ W *ᵥ y = d ∧ q ⬝ᵥ y < M := by
  classical
  rcases DJ.fm_alt' (σ := Fin m) (ι := Fin n) (fun j i => W i j) q with ⟨π, hπ⟩ | ⟨r, h0, h1, h2⟩
  · exfalso
    apply hnd
    refine ⟨π, fun j => ?_⟩
    have := hπ j
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (π i) (W i j))]
    exact this
  · have hWr : W *ᵥ r = 0 := by
      funext i
      have := h1 i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (W i j) (r j))]
      exact this
    have hqr : q ⬝ᵥ r < 0 := by
      simp only [dotProduct]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (q j) (r j))]
      exact h2
    set t : ℝ := max 0 ((q ⬝ᵥ y0 - M + 1) / (-(q ⬝ᵥ r))) with ht
    have ht0 : 0 ≤ t := le_max_left _ _
    have ht1 : (q ⬝ᵥ y0 - M + 1) / (-(q ⬝ᵥ r)) ≤ t := le_max_right _ _
    refine ⟨y0 + t • r, add_nonneg hy00 (smul_nonneg ht0 h0), ?_, ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hWr, smul_zero, add_zero, hy0]
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hpos : 0 < -(q ⬝ᵥ r) := by linarith
      have h3 : q ⬝ᵥ y0 - M + 1 ≤ t * (-(q ⬝ᵥ r)) := by
        rw [div_le_iff₀ hpos] at ht1; exact ht1
      nlinarith

lemma lpv_eq {q : Fin n → ℝ} {d : Fin m → ℝ} {y π} (hy0 : 0 ≤ y) (hy : W *ᵥ y = d)
    (hπ : π ᵥ* W ≤ q) (hle : q ⬝ᵥ y ≤ π ⬝ᵥ d) : lpv W q d = ((q ⬝ᵥ y : ℝ) : EReal) := by
  apply le_antisymm
  · exact sInf_le ⟨y, ⟨hy0, hy⟩, rfl⟩
  · apply le_sInf
    rintro _ ⟨y', ⟨hy'0, hy'⟩, rfl⟩
    exact EReal.coe_le_coe_iff.2 (le_trans hle (weak W hπ hy'0 hy'))

lemma lpv_bot {q : Fin n → ℝ} {d : Fin m → ℝ} {y0 : Fin n → ℝ} (hy00 : 0 ≤ y0) (hy0 : W *ᵥ y0 = d)
    (hnd : ¬ ∃ π : Fin m → ℝ, π ᵥ* W ≤ q) : lpv W q d = ⊥ := by
  rw [lpv, sInf_eq_bot]
  intro b hb
  induction b using EReal.rec with
  | bot => exact absurd hb (lt_irrefl _)
  | top =>
    obtain ⟨y, hy0', hy', -⟩ := unbdd W hy00 hy0 hnd 0
    exact ⟨_, ⟨y, ⟨hy0', hy'⟩, rfl⟩, EReal.coe_lt_top _⟩
  | coe r =>
    obtain ⟨y, hy0', hy', hlt⟩ := unbdd W hy00 hy0 hnd r
    exact ⟨_, ⟨y, ⟨hy0', hy'⟩, rfl⟩, EReal.coe_lt_coe_iff.2 hlt⟩

lemma lpv_top {q : Fin n → ℝ} {d : Fin m → ℝ} (hnp : ¬ ∃ y, 0 ≤ y ∧ W *ᵥ y = d) :
    lpv W q d = ⊤ := by
  rw [lpv, sInf_eq_top]
  rintro _ ⟨y, hy, rfl⟩
  exact absurd ⟨y, hy⟩ hnp


/-! ## Measurability of the LP value -/

def DF (q : Fin n → ℝ) : Prop := ∃ π : Fin m → ℝ, π ᵥ* W ≤ q
def PF (d : Fin m → ℝ) : Prop := ∃ y : Fin n → ℝ, 0 ≤ y ∧ W *ᵥ y = d

lemma df_iff (q : Fin n → ℝ) : DF W q ↔ ∀ r : Fin n → ℝ, 0 ≤ r → W *ᵥ r = 0 → 0 ≤ q ⬝ᵥ r := by
  classical
  constructor
  · rintro ⟨π, hπ⟩ r hr hWr
    have := weak W hπ hr hWr
    rwa [dotProduct_zero] at this
  · intro H
    rcases DJ.fm_alt' (σ := Fin m) (ι := Fin n) (fun j i => W i j) q with ⟨π, hπ⟩ | ⟨r, h0, h1, h2⟩
    · refine ⟨π, fun j => ?_⟩
      have := hπ j
      simp only [Matrix.vecMul, dotProduct]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (π i) (W i j))]
      exact this
    · exfalso
      have hWr : W *ᵥ r = 0 := by
        funext i
        have := h1 i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        rw [Finset.sum_congr rfl (fun j _ => mul_comm (W i j) (r j))]
        exact this
      have hqr : q ⬝ᵥ r < 0 := by
        simp only [dotProduct]
        rw [Finset.sum_congr rfl (fun j _ => mul_comm (q j) (r j))]
        exact h2
      have := H r h0 hWr
      linarith

lemma pf_iff (d : Fin m → ℝ) : PF W d ↔ ∀ π : Fin m → ℝ, 0 ≤ π ᵥ* W → 0 ≤ π ⬝ᵥ d := by
  classical
  constructor
  · rintro ⟨y, hy0, rfl⟩ π hπ
    rw [dotProduct_mulVec]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hy0 j)
  · intro H
    rcases DJ.fm_alt' (σ := Fin n) (ι := Fin m ⊕ (Fin m ⊕ Fin n))
        (Sum.elim (fun i j => W i j) (Sum.elim (fun i j => -W i j)
          (fun k j => if k = j then (-1 : ℝ) else 0)))
        (Sum.elim d (Sum.elim (-d) 0)) with ⟨y, hy⟩ | ⟨l, h0, h1, h2⟩
    · refine ⟨y, fun k => ?_, ?_⟩
      · have := hy (Sum.inr (Sum.inr k))
        simp only [Sum.elim_inr, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true, Pi.zero_apply] at this
        simp only [Pi.zero_apply]; linarith
      · funext i
        have e1 := hy (Sum.inl i)
        have e2 := hy (Sum.inr (Sum.inl i))
        simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, Pi.neg_apply,
          neg_le_neg_iff] at e1 e2
        simp only [Matrix.mulVec, dotProduct]
        linarith
    · exfalso
      set π : Fin m → ℝ := fun i => l (Sum.inl i) - l (Sum.inr (Sum.inl i))
      have hπW : ∀ j, (π ᵥ* W) j = l (Sum.inr (Sum.inr j)) := by
        intro j
        have := h1 j
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_neg, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        simp only [Matrix.vecMul, dotProduct, π, sub_mul, Finset.sum_sub_distrib]
        have e : ∑ x, -(l (Sum.inr (Sum.inl x)) * W x j) = -∑ x, l (Sum.inr (Sum.inl x)) * W x j :=
          Finset.sum_neg_distrib _
        linarith
      have hπd : π ⬝ᵥ d < 0 := by
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Pi.zero_apply,
          mul_neg, mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib] at h2
        simp only [dotProduct, π, sub_mul, Finset.sum_sub_distrib]
        linarith
      have := H π (fun j => by rw [hπW j]; exact h0 _)
      linarith

lemma df_closed : IsClosed {q : Fin n → ℝ | DF W q} := by
  have : {q : Fin n → ℝ | DF W q} =
      ⋂ r : Fin n → ℝ, ⋂ (_ : 0 ≤ r), ⋂ (_ : W *ᵥ r = 0), {q | 0 ≤ q ⬝ᵥ r} := by
    ext q; simp [df_iff]
  rw [this]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le continuous_const ?_
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

lemma pf_closed : IsClosed {d : Fin m → ℝ | PF W d} := by
  have : {d : Fin m → ℝ | PF W d} =
      ⋂ π : Fin m → ℝ, ⋂ (_ : 0 ≤ π ᵥ* W), {d | 0 ≤ π ⬝ᵥ d} := by
    ext d; simp [pf_iff]
  rw [this]
  refine isClosed_iInter fun π => isClosed_iInter fun _ => isClosed_le continuous_const ?_
  show Continuous fun d : Fin m → ℝ => ∑ i, π i * d i
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

/-- exact-penalty approximant -/
noncomputable def G (k : ℕ) (p : (Fin n → ℝ) × (Fin m → ℝ)) : EReal :=
  ⨅ y : {y : Fin n → ℝ // 0 ≤ y},
    ((p.1 ⬝ᵥ (y : Fin n → ℝ) + (k : ℝ) * ∑ i, |(W *ᵥ (y : Fin n → ℝ) - p.2) i| : ℝ) : EReal)

lemma G_meas (k : ℕ) : Measurable (G W k) := by
  apply UpperSemicontinuous.measurable
  apply upperSemicontinuous_iInf
  intro y
  apply Continuous.upperSemicontinuous
  apply continuous_coe_real_ereal.comp
  have h1 : Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) => p.1 ⬝ᵥ (y : Fin n → ℝ) := by
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).mul continuous_const
  have h2 : ∀ i, Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      |(W *ᵥ (y : Fin n → ℝ) - p.2) i| := fun i => by
    simp only [Pi.sub_apply]
    exact (continuous_const.sub ((continuous_apply i).comp continuous_snd)).abs
  exact h1.add (continuous_const.mul (continuous_finsetSum _ fun i _ => h2 i))

open Classical in
/-- measurable expression of the LP value -/
noncomputable def Qhat (p : (Fin n → ℝ) × (Fin m → ℝ)) : EReal :=
  if DF W p.1 then (if PF W p.2 then ⨆ k : ℕ, G W k p else ⊤) else (if PF W p.2 then ⊥ else ⊤)

lemma Qhat_meas : Measurable (Qhat W) := by
  classical
  have hD : MeasurableSet {p : (Fin n → ℝ) × (Fin m → ℝ) | DF W p.1} :=
    measurable_fst (df_closed W).measurableSet
  have hP : MeasurableSet {p : (Fin n → ℝ) × (Fin m → ℝ) | PF W p.2} :=
    measurable_snd (pf_closed W).measurableSet
  unfold Qhat
  exact Measurable.ite hD (Measurable.ite hP (Measurable.iSup fun k => G_meas W k) measurable_const)
    (Measurable.ite hP measurable_const measurable_const)

lemma lpv_eq_Qhat (q : Fin n → ℝ) (d : Fin m → ℝ) : lpv W q d = Qhat W (q, d) := by
  classical
  unfold Qhat
  by_cases hp : PF W d
  · have hp' := hp
    obtain ⟨y0, hy00, hy0⟩ := hp
    by_cases hd : DF W q
    · have hd' := hd
      obtain ⟨π0, hπ0⟩ := hd
      simp only [hd', hp', if_true]
      obtain ⟨y, π, hy, hyd, hπ, hle⟩ := strong W hπ0 hy00 hy0
      rw [lpv_eq W hy hyd hπ hle]
      apply le_antisymm
      · obtain ⟨k, hk⟩ := exists_nat_ge (∑ i, |π i|)
        refine le_iSup_of_le k (le_iInf fun z => ?_)
        obtain ⟨z, hz⟩ := z
        show ((q ⬝ᵥ y : ℝ) : EReal) ≤ ((q ⬝ᵥ z + (k : ℝ) * ∑ i, |(W *ᵥ z - d) i| : ℝ) : EReal)
        apply EReal.coe_le_coe_iff.2
        have hw := weak W hπ hz rfl
        set v := W *ᵥ z - d with hv
        have hS0 : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        have h1 : π ⬝ᵥ d - π ⬝ᵥ (W *ᵥ z) = -(π ⬝ᵥ v) := by
          rw [hv, dotProduct_sub]; ring
        have h2 : -(π ⬝ᵥ v) ≤ ∑ i, |π i| * |v i| := by
          refine (neg_le_abs _).trans ?_
          simp only [dotProduct]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
        have h3 : ∑ i, |π i| * |v i| ≤ (∑ i, |π i|) * ∑ i, |v i| := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)) (abs_nonneg _)
        have h4 : (∑ i, |π i|) * ∑ i, |v i| ≤ (k : ℝ) * ∑ i, |v i| :=
          mul_le_mul_of_nonneg_right hk hS0
        linarith
      · refine iSup_le fun k => iInf_le_of_le ⟨y, hy⟩ ?_
        show ((q ⬝ᵥ y + (k : ℝ) * ∑ i, |(W *ᵥ y - d) i| : ℝ) : EReal) ≤ ((q ⬝ᵥ y : ℝ) : EReal)
        simp [hyd]
    · simp only [hd, hp', if_true, if_false]
      exact lpv_bot W hy00 hy0 hd
  · rw [lpv_top W hp]
    simp only [hp, if_false]
    split_ifs <;> rfl

end P2MLP

set_option autoImplicit false

open Matrix

namespace P2MLP5

variable {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)

lemma lin (a b : Fin m → ℝ) (t : ℝ) : (a + t • b) ᵥ* W = a ᵥ* W + t • (b ᵥ* W) := by
  rw [Matrix.add_vecMul, Matrix.smul_vecMul]

lemma dlin (a b : Fin m → ℝ) (t : ℝ) (d : Fin m → ℝ) :
    (a + t • b) ⬝ᵥ d = a ⬝ᵥ d + t * (b ⬝ᵥ d) := by
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

/-- A direction vanishing on the active set of an optimal dual point does not improve it. -/
lemma dir_le (q : Fin n → ℝ) (d : Fin m → ℝ) (π : Fin m → ℝ) (hπ : π ᵥ* W ≤ q)
    (hopt : ∀ π' : Fin m → ℝ, π' ᵥ* W ≤ q → π' ⬝ᵥ d ≤ π ⬝ᵥ d)
    (f : Fin m → ℝ) (hf : ∀ j, (π ᵥ* W) j = q j → (f ᵥ* W) j = 0) : f ⬝ᵥ d ≤ 0 := by
  classical
  by_cases hneg : ∀ j, (f ᵥ* W) j ≤ 0
  · have h1 : (π + (1:ℝ) • f) ᵥ* W ≤ q := by
      rw [lin]
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      linarith [hπ j, hneg j]
    have := hopt _ h1
    rw [dlin] at this
    linarith
  · push Not at hneg
    obtain ⟨j0, hj0⟩ := hneg
    set S := Finset.univ.filter (fun j => 0 < (f ᵥ* W) j) with hS
    have hSne : S.Nonempty := ⟨j0, by simp [hS, hj0]⟩
    obtain ⟨js, hjsS, hjsmin⟩ := Finset.exists_min_image S
      (fun j => (q j - (π ᵥ* W) j) / (f ᵥ* W) j) hSne
    have hjs : 0 < (f ᵥ* W) js := by simpa [hS] using hjsS
    set t := (q js - (π ᵥ* W) js) / (f ᵥ* W) js with ht
    have hjsinact : (π ᵥ* W) js ≠ q js := fun h => by rw [hf js h] at hjs; exact lt_irrefl _ hjs
    have ht0 : 0 < t := by
      apply div_pos _ hjs
      have := hπ js
      have : (π ᵥ* W) js < q js := lt_of_le_of_ne this hjsinact
      linarith
    have hfeas : (π + t • f) ᵥ* W ≤ q := by
      rw [lin]
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : 0 < (f ᵥ* W) j
      · have hjS : j ∈ S := by simp [hS, hj]
        have hle := hjsmin j hjS
        rw [le_div_iff₀ hj] at hle
        linarith
      · push Not at hj
        have := hπ j
        nlinarith
    have := hopt _ hfeas
    rw [dlin] at this
    have : t * (f ⬝ᵥ d) ≤ 0 := by linarith
    by_contra hc
    push Not at hc
    have := mul_pos ht0 hc
    linarith

/-- active set -/
noncomputable def act (q : Fin n → ℝ) (π : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (π ᵥ* W) j = q j)

lemma step (q : Fin n → ℝ) (d : Fin m → ℝ) (π : Fin m → ℝ) (hπ : π ᵥ* W ≤ q)
    (hopt : ∀ π' : Fin m → ℝ, π' ᵥ* W ≤ q → π' ⬝ᵥ d ≤ π ⬝ᵥ d)
    (H : ¬ ∀ e : Fin m → ℝ, (∀ j, (π ᵥ* W) j = q j → (e ᵥ* W) j = 0) → e ᵥ* W = 0) :
    ∃ π2 : Fin m → ℝ, π2 ᵥ* W ≤ q ∧ π2 ⬝ᵥ d = π ⬝ᵥ d ∧
      (act W q π).card < (act W q π2).card := by
  classical
  push Not at H
  obtain ⟨e0, he0, hne⟩ := H
  obtain ⟨j0, hj0⟩ : ∃ j, (e0 ᵥ* W) j ≠ 0 := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  -- orient e so that it has a positive coordinate at j0
  obtain ⟨e, he, hej0⟩ : ∃ e : Fin m → ℝ, (∀ j, (π ᵥ* W) j = q j → (e ᵥ* W) j = 0) ∧
      0 < (e ᵥ* W) j0 := by
    rcases lt_or_gt_of_ne hj0 with h | h
    · refine ⟨-e0, fun j hj => ?_, ?_⟩
      · rw [Matrix.neg_vecMul]; simp [he0 j hj]
      · rw [Matrix.neg_vecMul]; simp only [Pi.neg_apply]; linarith
    · exact ⟨e0, he0, h⟩
  have hed1 := dir_le W q d π hπ hopt e he
  have hed2 := dir_le W q d π hπ hopt (-e) (fun j hj => by rw [Matrix.neg_vecMul]; simp [he j hj])
  rw [neg_dotProduct] at hed2
  have hed : e ⬝ᵥ d = 0 := by linarith
  set S := Finset.univ.filter (fun j => 0 < (e ᵥ* W) j) with hS
  have hSne : S.Nonempty := ⟨j0, by simp [hS, hej0]⟩
  obtain ⟨js, hjsS, hjsmin⟩ := Finset.exists_min_image S
    (fun j => (q j - (π ᵥ* W) j) / (e ᵥ* W) j) hSne
  have hjs : 0 < (e ᵥ* W) js := by simpa [hS] using hjsS
  set t := (q js - (π ᵥ* W) js) / (e ᵥ* W) js with ht
  have hjsinact : (π ᵥ* W) js ≠ q js := fun h => by rw [he js h] at hjs; exact lt_irrefl _ hjs
  have ht0 : 0 ≤ t := by
    apply div_nonneg _ hjs.le
    linarith [hπ js]
  refine ⟨π + t • e, ?_, ?_, ?_⟩
  · rw [lin]
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : 0 < (e ᵥ* W) j
    · have hjS : j ∈ S := by simp [hS, hj]
      have hle := hjsmin j hjS
      rw [le_div_iff₀ hj] at hle
      linarith
    · push Not at hj
      have := hπ j
      nlinarith
  · rw [dlin, hed, mul_zero, add_zero]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨js, ?_, ?_⟩
      · simp only [act, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [lin]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
        field_simp
        ring
      · simp only [act, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hjsinact
    · intro j hj
      simp only [act, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [lin]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he j hj, mul_zero, add_zero]
      exact hj

lemma reduce (q : Fin n → ℝ) (d : Fin m → ℝ) :
    ∀ k : ℕ, ∀ π : Fin m → ℝ, π ᵥ* W ≤ q →
      (∀ π' : Fin m → ℝ, π' ᵥ* W ≤ q → π' ⬝ᵥ d ≤ π ⬝ᵥ d) →
      n - (act W q π).card ≤ k →
      ∃ π1 : Fin m → ℝ, π1 ᵥ* W ≤ q ∧ π1 ⬝ᵥ d = π ⬝ᵥ d ∧
        ∀ e : Fin m → ℝ, (∀ j, (π1 ᵥ* W) j = q j → (e ᵥ* W) j = 0) → e ᵥ* W = 0 := by
  intro k
  induction k with
  | zero =>
    intro π hπ hopt hk
    by_cases H : ∀ e : Fin m → ℝ, (∀ j, (π ᵥ* W) j = q j → (e ᵥ* W) j = 0) → e ᵥ* W = 0
    · exact ⟨π, hπ, rfl, H⟩
    · obtain ⟨π2, -, -, hc⟩ := step W q d π hπ hopt H
      have : (act W q π2).card ≤ n := by
        calc (act W q π2).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := Finset.card_fin n
      omega
  | succ k ih =>
    intro π hπ hopt hk
    by_cases H : ∀ e : Fin m → ℝ, (∀ j, (π ᵥ* W) j = q j → (e ᵥ* W) j = 0) → e ᵥ* W = 0
    · exact ⟨π, hπ, rfl, H⟩
    · obtain ⟨π2, hπ2, hd2, hc⟩ := step W q d π hπ hopt H
      have : (act W q π2).card ≤ n := by
        calc (act W q π2).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := Finset.card_fin n
      have hopt2 : ∀ π' : Fin m → ℝ, π' ᵥ* W ≤ q → π' ⬝ᵥ d ≤ π2 ⬝ᵥ d := by
        intro π' h'; rw [hd2]; exact hopt π' h'
      obtain ⟨π1, h1, h2, h3⟩ := ih π2 hπ2 hopt2 (by omega)
      exact ⟨π1, h1, by rw [h2, hd2], h3⟩

/-- coordinate mask -/
noncomputable def maskL (J : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi (fun j => if j ∈ J then LinearMap.proj j else 0)

lemma maskL_apply (J : Finset (Fin n)) (v : Fin n → ℝ) (j : Fin n) :
    maskL J v j = if j ∈ J then v j else 0 := by
  unfold maskL
  by_cases h : j ∈ J <;> simp [h]

lemma per_J (J : Finset (Fin n)) : ∃ K : ℝ, 0 ≤ K ∧
    ((∀ e : Fin m → ℝ, (∀ j ∈ J, (e ᵥ* W) j = 0) → e ᵥ* W = 0) →
      ∀ σ : Fin m → ℝ, ‖σ ᵥ* W‖ ≤ K * ‖maskL J (σ ᵥ* W)‖) := by
  classical
  by_cases H : ∀ e : Fin m → ℝ, (∀ j ∈ J, (e ᵥ* W) j = 0) → e ᵥ* W = 0
  · set E := LinearMap.range W.vecMulLinear
    let ρ : E →ₗ[ℝ] (Fin n → ℝ) := (maskL J).comp E.subtype
    have hker : LinearMap.ker ρ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨x, hx⟩ hρ
      obtain ⟨σ, rfl⟩ := LinearMap.mem_range.1 hx
      apply Subtype.ext
      simp only [Submodule.coe_zero]
      apply H σ
      intro j hj
      have := congrFun hρ j
      simp only [ρ, LinearMap.comp_apply, Submodule.subtype_apply, maskL_apply, if_pos hj,
        Pi.zero_apply] at this
      simpa using this
    obtain ⟨K, -, hK⟩ := ρ.exists_antilipschitzWith hker
    refine ⟨K, K.2, fun _ σ => ?_⟩
    have := hK.le_mul_dist (⟨σ ᵥ* W, LinearMap.mem_range.2 ⟨σ, rfl⟩⟩ : E) 0
    rw [dist_zero_right, map_zero, dist_zero_right] at this
    exact this
  · exact ⟨0, le_rfl, fun h => absurd h H⟩

theorem lp5 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Fin n → ℝ) (d : Fin m → ℝ) (y0 : Fin n → ℝ),
    W *ᵥ y0 = d → ∀ π : Fin m → ℝ, π ᵥ* W ≤ q →
      (∀ π' : Fin m → ℝ, π' ᵥ* W ≤ q → π' ⬝ᵥ d ≤ π ⬝ᵥ d) →
      ∃ π' : Fin m → ℝ, π' ᵥ* W ≤ q ∧ π' ⬝ᵥ d = π ⬝ᵥ d ∧ ‖π'‖ ≤ C * ‖q‖ := by
  classical
  choose K hK0 hK using per_J W
  set E := LinearMap.range W.vecMulLinear
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    (W.vecMulLinear.rangeRestrict) (LinearMap.range_rangeRestrict _)
  let G : E →L[ℝ] (Fin m → ℝ) := LinearMap.toContinuousLinearMap g
  refine ⟨‖G‖ * ∑ J : Finset (Fin n), K J,
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg G) (Finset.sum_nonneg fun J _ => hK0 J), ?_⟩
  intro q d y0 hd π hπ hopt
  obtain ⟨π1, h1, h2, h3⟩ := reduce W q d (n - (act W q π).card) π hπ hopt le_rfl
  set s : E := ⟨π1 ᵥ* W, LinearMap.mem_range.2 ⟨π1, rfl⟩⟩
  have hgs : g s ᵥ* W = π1 ᵥ* W := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg s)
    simpa [s] using this
  refine ⟨g s, by rw [hgs]; exact h1, ?_, ?_⟩
  · rw [← h2, ← hd, dotProduct_mulVec, dotProduct_mulVec, hgs]
  · set J := act W q π1
    have hJ : ∀ e : Fin m → ℝ, (∀ j ∈ J, (e ᵥ* W) j = 0) → e ᵥ* W = 0 := by
      intro e he
      apply h3 e
      intro j hj
      exact he j (by simp [J, act, hj])
    have hb := hK J hJ π1
    have hmask : ‖maskL J (π1 ᵥ* W)‖ ≤ ‖q‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
      rw [maskL_apply]
      split_ifs with hj
      · have : (π1 ᵥ* W) j = q j := by simpa [J, act] using hj
        rw [this]; exact norm_le_pi_norm q j
      · simp
    have hGs : ‖g s‖ ≤ ‖G‖ * ‖s‖ := G.le_opNorm s
    have hsn : ‖s‖ = ‖π1 ᵥ* W‖ := rfl
    have hKle : K J ≤ ∑ J' : Finset (Fin n), K J' :=
      Finset.single_le_sum (fun J' _ => hK0 J') (Finset.mem_univ J)
    calc ‖g s‖ ≤ ‖G‖ * ‖s‖ := hGs
      _ ≤ ‖G‖ * (K J * ‖q‖) := by
          rw [hsn]
          apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg G)
          exact hb.trans (mul_le_mul_of_nonneg_left hmask (hK0 J))
      _ ≤ ‖G‖ * ((∑ J' : Finset (Fin n), K J') * ‖q‖) := by
          apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg G)
          exact mul_le_mul_of_nonneg_right hKle (norm_nonneg _)
      _ = ‖G‖ * (∑ J' : Finset (Fin n), K J') * ‖q‖ := by ring

end P2MLP5

/-! ## theorem_6a: finiteness, convexity, Lipschitz continuity of the expected recourse -/

namespace P2MSix

open MeasureTheory Matrix StochasticProg.RecourseKKT P2MLP

lemma attain {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) {q : Fin n → ℝ} {d : Fin m → ℝ}
    (hq : DF W q) (hd : PF W d) :
    ∃ y : Fin n → ℝ, 0 ≤ y ∧ W *ᵥ y = d ∧ lpv W q d = ((q ⬝ᵥ y : ℝ) : EReal) := by
  obtain ⟨π0, hπ0⟩ := hq
  obtain ⟨y0, hy00, hy0⟩ := hd
  obtain ⟨y, π, hy, hyd, hπ, hle⟩ := strong W hπ0 hy00 hy0
  exact ⟨y, hy, hyd, lpv_eq W hy hyd hπ hle⟩

lemma lpv_ge {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) {q : Fin n → ℝ} {d : Fin m → ℝ}
    {π : Fin m → ℝ} (hπ : π ᵥ* W ≤ q) : ((π ⬝ᵥ d : ℝ) : EReal) ≤ lpv W q d := by
  apply le_sInf
  rintro _ ⟨y, ⟨hy0, hy⟩, rfl⟩
  exact EReal.coe_le_coe_iff.2 (weak W hπ hy0 hy)

lemma dual_bd {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : Fin n → ℝ) (d : Fin m → ℝ), DF W q → PF W d →
      ∃ π : Fin m → ℝ, π ᵥ* W ≤ q ∧ lpv W q d = ((π ⬝ᵥ d : ℝ) : EReal) ∧ ‖π‖ ≤ C * ‖q‖ := by
  obtain ⟨C, hC0, hC⟩ := P2MLP5.lp5 W
  refine ⟨C, hC0, fun q d hq hd => ?_⟩
  obtain ⟨π0, hπ0⟩ := hq
  obtain ⟨y0, hy00, hy0⟩ := hd
  obtain ⟨y, π, hy, hyd, hπ, hle⟩ := strong W hπ0 hy00 hy0
  have hopt : ∀ π' : Fin m → ℝ, π' ᵥ* W ≤ q → π' ⬝ᵥ d ≤ π ⬝ᵥ d :=
    fun π' h' => (weak W h' hy hyd).trans hle
  obtain ⟨π', h1, h2, h3⟩ := hC q d y hyd π hπ hopt
  refine ⟨π', h1, ?_, h3⟩
  rw [lpv_eq W hy hyd hπ hle, h2]
  have := weak W hπ hy hyd
  rw [le_antisymm hle this]

lemma dot_bd {m : ℕ} (π d : Fin m → ℝ) : |π ⬝ᵥ d| ≤ m * (‖π‖ * ‖d‖) := by
  simp only [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ (Finset.univ : Finset (Fin m)), |π i * d i| ≤ ‖π‖ * ‖d‖ := by
    intro i _
    rw [abs_mul]
    have h1 : |π i| ≤ ‖π‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm π i
    have h2 : |d i| ≤ ‖d‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d i
    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  simp

lemma norm_le_sum {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ≤ ∑ j, |v j| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun k _ => abs_nonneg (v k)) (Finset.mem_univ j)

/-- `‖T v‖ ≤ (∑ |T i j|) ‖v‖` -/
lemma mulVec_bd {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    ‖T *ᵥ v‖ ≤ (∑ i, ∑ j, |T i j|) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => abs_nonneg _) (norm_nonneg _))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin n)), |T i j * v j| ≤ |T i j| * ‖v‖ := by
    intro j _
    rw [abs_mul]
    have : |v j| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.single_le_sum (f := fun i => ∑ j, |T i j|)
    (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)

variable {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}

/-- second-stage right-hand side -/
def dx (pb : RecourseData Ω n1 m1 n2 m2) (x : Fin n1 → ℝ) (ω : Ω) : Fin m2 → ℝ :=
  pb.h ω - pb.T ω *ᵥ x

lemma Q_eq (pb : RecourseData Ω n1 m1 n2 m2) (x : Fin n1 → ℝ) (ω : Ω) :
    secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x = lpv pb.W (pb.q ω) (dx pb x ω) := rfl

lemma dx_meas (pb : RecourseData Ω n1 m1 n2 m2) (x : Fin n1 → ℝ) : Measurable (dx pb x) := by
  apply measurable_pi_lambda
  intro i
  simp only [dx, Pi.sub_apply, Matrix.mulVec, dotProduct]
  exact (pb.measurable_h i).sub
    (Finset.measurable_sum _ fun j _ => (pb.measurable_T i j).mul measurable_const)

lemma Q_meas (pb : RecourseData Ω n1 m1 n2 m2) (x : Fin n1 → ℝ) :
    Measurable fun ω => secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x := by
  have : (fun ω => secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x) =
      Qhat pb.W ∘ (fun ω => (pb.q ω, dx pb x ω)) := by
    funext ω
    rw [Q_eq, lpv_eq_Qhat]
    rfl
  rw [this]
  exact (Qhat_meas pb.W).comp ((measurable_pi_lambda _ pb.measurable_q).prodMk (dx_meas pb x))

/-- the square-integrable envelope -/
noncomputable def s2 (pb : RecourseData Ω n1 m1 n2 m2) (ω : Ω) : ℝ :=
  (∑ j, |pb.q ω j|) ^ 2 + (∑ i, |pb.h ω i|) ^ 2 + (∑ i, ∑ j, |pb.T ω i j|) ^ 2

lemma s2_int (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) (hmom : FiniteSecondMoments P pb) :
    Integrable (s2 pb) P := by
  obtain ⟨hq, hh, hT⟩ := hmom
  have ha : MemLp (fun ω => ∑ j, |pb.q ω j|) 2 P :=
    memLp_finsetSum _ fun j _ => (hq j).abs
  have hb : MemLp (fun ω => ∑ i, |pb.h ω i|) 2 P :=
    memLp_finsetSum _ fun i _ => (hh i).abs
  have ht : MemLp (fun ω => ∑ i, ∑ j, |pb.T ω i j|) 2 P :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => (hT i j).abs
  exact (ha.integrable_sq.add hb.integrable_sq).add ht.integrable_sq

lemma s2_nonneg (pb : RecourseData Ω n1 m1 n2 m2) (ω : Ω) : 0 ≤ s2 pb ω := by
  unfold s2; positivity

/-- pointwise value bound on good realizations -/
lemma val_bd (pb : RecourseData Ω n1 m1 n2 m2) (C : ℝ) (hC0 : 0 ≤ C) (x : Fin n1 → ℝ) (ω : Ω)
    (π : Fin m2 → ℝ) (hπ : ‖π‖ ≤ C * ‖pb.q ω‖) :
    |π ⬝ᵥ dx pb x ω| ≤ m2 * C * (s2 pb ω * (1 + ‖x‖)) := by
  set a := ∑ j, |pb.q ω j|
  set b := ∑ i, |pb.h ω i|
  set t := ∑ i, ∑ j, |pb.T ω i j|
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun j _ => abs_nonneg _
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hqa : ‖pb.q ω‖ ≤ a := norm_le_sum _
  have hd : ‖dx pb x ω‖ ≤ b + t * ‖x‖ := by
    unfold dx
    refine (norm_sub_le _ _).trans (add_le_add (norm_le_sum _) (mulVec_bd _ _))
  have hπa : ‖π‖ ≤ C * a := hπ.trans (mul_le_mul_of_nonneg_left hqa hC0)
  have hs : s2 pb ω = a ^ 2 + b ^ 2 + t ^ 2 := rfl
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have key : a * (b + t * ‖x‖) ≤ s2 pb ω * (1 + ‖x‖) := by
    rw [hs]
    have e1 : a * b ≤ a ^ 2 + b ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg t]
    have e2 : a * t ≤ a ^ 2 + b ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (a - t), sq_nonneg b]
    nlinarith [mul_le_mul_of_nonneg_right e2 hx0]
  have hm0 : (0 : ℝ) ≤ m2 := Nat.cast_nonneg _
  calc |π ⬝ᵥ dx pb x ω| ≤ m2 * (‖π‖ * ‖dx pb x ω‖) := dot_bd _ _
    _ ≤ m2 * ((C * a) * (b + t * ‖x‖)) := by
        apply mul_le_mul_of_nonneg_left _ hm0
        exact mul_le_mul hπa hd (norm_nonneg _) (mul_nonneg hC0 ha0)
    _ = m2 * C * (a * (b + t * ‖x‖)) := by ring
    _ ≤ m2 * C * (s2 pb ω * (1 + ‖x‖)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hm0 hC0)

lemma toENN_coe (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

lemma ER_eq (P : Measure Ω) [IsFiniteMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (hmom : FiniteSecondMoments P pb) (x : Fin n1 → ℝ)
    (hgood : ∀ᵐ ω ∂P, DF pb.W (pb.q ω) ∧ PF pb.W (dx pb x ω)) :
    Integrable (fun ω => (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal) P ∧
      expectedRecourse P pb x =
        ((∫ ω, (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal ∂P : ℝ) : EReal) := by
  obtain ⟨C, hC0, hC⟩ := dual_bd pb.W
  set F := fun ω => secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x with hF
  set f := fun ω => (F ω).toReal with hf
  have hcoe : ∀ᵐ ω ∂P, F ω = ((f ω : ℝ) : EReal) ∧
      |f ω| ≤ m2 * C * (s2 pb ω * (1 + ‖x‖)) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨π, -, hv, hπ⟩ := hC _ _ hω.1 hω.2
    have hFω : F ω = ((π ⬝ᵥ dx pb x ω : ℝ) : EReal) := hv
    have hfω : f ω = π ⬝ᵥ dx pb x ω := by simp only [hf, hFω, EReal.toReal_coe]
    refine ⟨by rw [hFω, hfω], ?_⟩
    rw [hfω]
    exact val_bd pb C hC0 x ω π hπ
  have hint : Integrable f P := by
    refine Integrable.mono' (((s2_int P pb hmom).mul_const (1 + ‖x‖)).const_mul (m2 * C))
      ((Q_meas pb x).ereal_toReal.aestronglyMeasurable) ?_
    filter_upwards [hcoe] with ω hω
    rw [Real.norm_eq_abs]
    exact hω.2
  refine ⟨hint, ?_⟩
  have hpos : ∫⁻ ω, (F ω).toENNReal ∂P = ∫⁻ ω, ENNReal.ofReal (f ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hcoe] with ω hω
    rw [hω.1, toENN_coe]
  have hneg : ∫⁻ ω, (-(F ω)).toENNReal ∂P = ∫⁻ ω, ENNReal.ofReal (-f ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hcoe] with ω hω
    rw [hω.1, ← EReal.coe_neg, toENN_coe]
  have h1 := hint.lintegral_lt_top
  have h2 := hint.neg.lintegral_lt_top
  simp only [Pi.neg_apply] at h2
  unfold expectedRecourse
  simp only []
  change (if ∫⁻ ω, (F ω).toENNReal ∂P = ⊤ then ⊤ else
      ((∫⁻ ω, (F ω).toENNReal ∂P : ENNReal) : EReal) - ((∫⁻ ω, (-(F ω)).toENNReal ∂P : ENNReal) : EReal))
    = ((∫ ω, f ω ∂P : ℝ) : EReal)
  rw [hpos, hneg, if_neg h1.ne, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    EReal.coe_sub, EReal.coe_ennreal_toReal h1.ne, EReal.coe_ennreal_toReal h2.ne]

lemma ae_good (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2)
    (hnn : RecourseNotNegInf P pb) (x : Fin n1 → ℝ) (hx : x ∈ secondStageFeasSet P pb) :
    ∀ᵐ ω ∂P, DF pb.W (pb.q ω) ∧ PF pb.W (dx pb x ω) := by
  have hpos : ∫⁻ ω, (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toENNReal ∂P ≠ ⊤ := by
    intro h
    have hx' : expectedRecourse P pb x < ⊤ := hx
    unfold expectedRecourse at hx'
    simp only [h, if_true] at hx'
    exact lt_irrefl _ hx'
  have hlt := ae_lt_top (Q_meas pb x).ereal_toENNReal hpos
  filter_upwards [hlt, hnn x] with ω h1 h2
  rw [Q_eq] at h1 h2
  have hpf : PF pb.W (dx pb x ω) := by
    by_contra hc
    rw [lpv_top pb.W hc] at h1
    simp at h1
  refine ⟨?_, hpf⟩
  by_contra hc
  obtain ⟨y0, hy00, hy0⟩ := hpf
  exact h2 (lpv_bot pb.W hy00 hy0 hc)

lemma dx_comb (pb : RecourseData Ω n1 m1 n2 m2) (x x' : Fin n1 → ℝ) (a b : ℝ) (hab : a + b = 1)
    (ω : Ω) : dx pb (a • x + b • x') ω = a • dx pb x ω + b • dx pb x' ω := by
  obtain rfl : b = 1 - a := by linarith
  unfold dx
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma pf_comb {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) {d1 d2 : Fin m → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : PF W d1) (h2 : PF W d2) : PF W (a • d1 + b • d2) := by
  obtain ⟨y1, hy1, rfl⟩ := h1
  obtain ⟨y2, hy2, rfl⟩ := h2
  refine ⟨a • y1 + b • y2, add_nonneg (smul_nonneg ha hy1) (smul_nonneg hb hy2), ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem six (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (hmom : FiniteSecondMoments P pb) (hnn : RecourseNotNegInf P pb) :
    (∀ x ∈ secondStageFeasSet P pb, expectedRecourse P pb x ≠ ⊥) ∧
    ConvexOn ℝ (secondStageFeasSet P pb) (fun x => (expectedRecourse P pb x).toReal) ∧
    ∃ L : NNReal, LipschitzOnWith L (fun x => (expectedRecourse P pb x).toReal)
      (secondStageFeasSet P pb) := by
  set K2 := secondStageFeasSet P pb with hK2
  have hER : ∀ x ∈ K2, expectedRecourse P pb x =
      ((∫ ω, (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal ∂P : ℝ) : EReal) :=
    fun x hx => (ER_eq P pb hmom x (ae_good P pb hnn x hx)).2
  have hI : ∀ x ∈ K2,
      Integrable (fun ω => (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal) P :=
    fun x hx => (ER_eq P pb hmom x (ae_good P pb hnn x hx)).1
  have hTR : ∀ x ∈ K2, (expectedRecourse P pb x).toReal =
      ∫ ω, (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal ∂P := by
    intro x hx; rw [hER x hx, EReal.toReal_coe]
  refine ⟨fun x hx => by rw [hER x hx]; exact EReal.coe_ne_bot _, ?_, ?_⟩
  · -- convexity
    have hgoodc : ∀ x ∈ K2, ∀ x' ∈ K2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        ∀ᵐ ω ∂P, DF pb.W (pb.q ω) ∧ PF pb.W (dx pb (a • x + b • x') ω) := by
      intro x hx x' hx' a b ha hb hab
      filter_upwards [ae_good P pb hnn x hx, ae_good P pb hnn x' hx'] with ω h1 h2
      refine ⟨h1.1, ?_⟩
      rw [dx_comb pb x x' a b hab ω]
      exact pf_comb pb.W ha hb h1.2 h2.2
    have hmem : ∀ x ∈ K2, ∀ x' ∈ K2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • x + b • x' ∈ K2 := by
      intro x hx x' hx' a b ha hb hab
      show expectedRecourse P pb (a • x + b • x') < ⊤
      rw [(ER_eq P pb hmom _ (hgoodc x hx x' hx' a b ha hb hab)).2]
      exact EReal.coe_lt_top _
    refine ⟨fun x hx x' hx' a b ha hb hab => hmem x hx x' hx' a b ha hb hab, ?_⟩
    intro x hx x' hx' a b ha hb hab
    have hz := hmem x hx x' hx' a b ha hb hab
    simp only []
    rw [hTR _ hz, hTR x hx, hTR x' hx', smul_eq_mul, smul_eq_mul, ← integral_const_mul,
      ← integral_const_mul, ← integral_add ((hI x hx).const_mul a) ((hI x' hx').const_mul b)]
    apply integral_mono_ae (hI _ hz) (((hI x hx).const_mul a).add ((hI x' hx').const_mul b))
    filter_upwards [ae_good P pb hnn x hx, ae_good P pb hnn x' hx'] with ω h1 h2
    obtain ⟨y1, hy1, hy1d, hv1⟩ := attain pb.W h1.1 h1.2
    obtain ⟨y2, hy2, hy2d, hv2⟩ := attain pb.W h2.1 h2.2
    have hfe : (pb.q ω) ⬝ᵥ (a • y1 + b • y2) = a * (pb.q ω ⬝ᵥ y1) + b * (pb.q ω ⬝ᵥ y2) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hle : secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) (a • x + b • x') ≤
        ((a * (pb.q ω ⬝ᵥ y1) + b * (pb.q ω ⬝ᵥ y2) : ℝ) : EReal) := by
      rw [Q_eq, ← hfe]
      apply sInf_le
      refine ⟨a • y1 + b • y2, ⟨add_nonneg (smul_nonneg ha hy1) (smul_nonneg hb hy2), ?_⟩, rfl⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hy1d, hy2d,
        dx_comb pb x x' a b hab ω]
    have hbot : secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) (a • x + b • x') ≠ ⊥ := by
      rw [Q_eq]
      obtain ⟨π0, hπ0⟩ := h1.1
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (lpv_ge pb.W hπ0)
    show (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) (a • x + b • x')).toReal ≤
      a * (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal +
      b * (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x').toReal
    rw [Q_eq pb x, Q_eq pb x', hv1, hv2, EReal.toReal_coe, EReal.toReal_coe]
    have := EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  · -- Lipschitz
    obtain ⟨C, hC0, hC⟩ := dual_bd pb.W
    set K0 : ℝ := m2 * C * ∫ ω, s2 pb ω ∂P with hK0
    have hK00 : 0 ≤ K0 := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0)
      (integral_nonneg fun ω => s2_nonneg pb ω)
    refine ⟨Real.toNNReal K0, LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_⟩
    rw [Real.coe_toNNReal _ hK00, Real.dist_eq, hTR x hx, hTR x' hx',
      ← integral_sub (hI x hx) (hI x' hx'), dist_eq_norm]
    have hpt : ∀ u ∈ K2, ∀ u' ∈ K2, ∀ᵐ ω ∂P,
        (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) u).toReal -
          (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) u').toReal ≤
        m2 * C * s2 pb ω * ‖u - u'‖ := by
      intro u hu u' hu'
      filter_upwards [ae_good P pb hnn u hu, ae_good P pb hnn u' hu'] with ω h1 h2
      obtain ⟨π, hπW, hv, hπ⟩ := hC _ _ h1.1 h1.2
      have hge := lpv_ge pb.W (d := dx pb u' ω) hπW
      obtain ⟨y2, -, -, hv2⟩ := attain pb.W h2.1 h2.2
      rw [Q_eq pb u, Q_eq pb u', hv, hv2, EReal.toReal_coe, EReal.toReal_coe]
      rw [hv2] at hge
      have hge' := EReal.coe_le_coe_iff.1 hge
      have hdiff : dx pb u ω - dx pb u' ω = pb.T ω *ᵥ (u' - u) := by
        unfold dx
        rw [Matrix.mulVec_sub]
        abel
      have h3 : π ⬝ᵥ dx pb u ω - π ⬝ᵥ dx pb u' ω ≤ |π ⬝ᵥ (pb.T ω *ᵥ (u' - u))| := by
        rw [← dotProduct_sub, hdiff]; exact le_abs_self _
      have h4 : |π ⬝ᵥ (pb.T ω *ᵥ (u' - u))| ≤ m2 * (‖π‖ * ‖pb.T ω *ᵥ (u' - u)‖) := dot_bd _ _
      set a := ∑ j, |pb.q ω j|
      set t := ∑ i, ∑ j, |pb.T ω i j|
      have ha0 : 0 ≤ a := Finset.sum_nonneg fun j _ => abs_nonneg _
      have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
      have hπa : ‖π‖ ≤ C * a := hπ.trans (mul_le_mul_of_nonneg_left (norm_le_sum _) hC0)
      have hTv : ‖pb.T ω *ᵥ (u' - u)‖ ≤ t * ‖u - u'‖ := by
        rw [norm_sub_rev u u']; exact mulVec_bd _ _
      have hat : a * t ≤ s2 pb ω := by
        show a * t ≤ a ^ 2 + (∑ i, |pb.h ω i|) ^ 2 + t ^ 2
        nlinarith [sq_nonneg (a - t), sq_nonneg (∑ i, |pb.h ω i|)]
      have hm0 : (0 : ℝ) ≤ m2 := Nat.cast_nonneg _
      have hn0 : 0 ≤ ‖u - u'‖ := norm_nonneg _
      have h5 : m2 * (‖π‖ * ‖pb.T ω *ᵥ (u' - u)‖) ≤ m2 * ((C * a) * (t * ‖u - u'‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hπa hTv (norm_nonneg _) (mul_nonneg hC0 ha0)) hm0
      have h6 : m2 * ((C * a) * (t * ‖u - u'‖)) ≤ m2 * C * s2 pb ω * ‖u - u'‖ := by
        have : m2 * ((C * a) * (t * ‖u - u'‖)) = (m2 * C) * (a * t) * ‖u - u'‖ := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hat (mul_nonneg hm0 hC0)) hn0
      linarith
    have hbd : ∀ᵐ ω ∂P, ‖(secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toReal -
          (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x').toReal‖ ≤
        m2 * C * s2 pb ω * ‖x - x'‖ := by
      filter_upwards [hpt x hx x' hx', hpt x' hx' x hx] with ω h1 h2
      rw [Real.norm_eq_abs, abs_le]
      rw [norm_sub_rev x' x] at h2
      constructor <;> linarith
    have hgi : Integrable (fun ω => m2 * C * s2 pb ω * ‖x - x'‖) P :=
      ((s2_int P pb hmom).const_mul (m2 * C)).mul_const _
    refine (norm_integral_le_of_norm_le hgi hbd).trans (le_of_eq ?_)
    rw [integral_mul_const, integral_const_mul, hK0]

end P2MSix

section KKT9
open MeasureTheory Matrix StochasticProg.RecourseKKT

/-- theorem_6a's conclusion, as a predicate. -/
def Six (Ω : Type*) [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ} (P : Measure Ω)
    (pb : RecourseData Ω n1 m1 n2 m2) : Prop :=
  (∀ x ∈ secondStageFeasSet P pb, expectedRecourse P pb x ≠ ⊥) ∧
    ConvexOn ℝ (secondStageFeasSet P pb) (fun x => (expectedRecourse P pb x).toReal) ∧
    ∃ L : NNReal, LipschitzOnWith L (fun x => (expectedRecourse P pb x).toReal)
      (secondStageFeasSet P pb)

lemma coc_of_6a {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) (h6 : Six Ω P pb)
    (hfin : HasFiniteOptimalValue P pb)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b)
    (hR : (firstStageSet pb.A pb.b ∩ intrinsicInterior ℝ (secondStageFeasSet P pb)).Nonempty ∨
          IsPolyhedralSet (secondStageFeasSet P pb) ∨
          firstStageSet pb.A pb.b ⊆ secondStageFeasSet P pb)
    (hopt : IsOptimalDEP P pb xs) :
    ∃ ζ : Fin n1 → ℝ, (expectedRecourse P pb xs ≠ ⊤) ∧
      (∀ w ∈ secondStageFeasSet P pb, (expectedRecourse P pb xs).toReal + ζ ⬝ᵥ (w - xs) ≤
        (expectedRecourse P pb w).toReal) ∧
      ∀ x ∈ firstStageSet pb.A pb.b, 0 ≤ (pb.c + ζ) ⬝ᵥ (x - xs) := by
  obtain ⟨hbot, hconv, L, hL⟩ := h6
  set K1 := firstStageSet pb.A pb.b with hK1
  set K2 := secondStageFeasSet P pb with hK2
  have hcoe : ∀ x ∈ K2, expectedRecourse P pb x = ((expectedRecourse P pb x).toReal : EReal) :=
    fun x hx => (EReal.coe_toReal (ne_of_lt hx) (hbot x hx)).symm
  -- xs has a finite objective
  have hval : depObjective P pb xs = ⨅ x ∈ K1, depObjective P pb x :=
    le_antisymm (le_iInf₂ fun x hx => hopt.2 x hx) (iInf₂_le xs hxs)
  have hxs2 : xs ∈ K2 := by
    show expectedRecourse P pb xs < ⊤
    rw [lt_top_iff_ne_top]
    intro htop
    apply hfin.1
    rw [← hval]
    unfold depObjective
    rw [htop, EReal.coe_add_top]
  have hopt' : ∀ x ∈ K1, x ∈ K2 → pb.c ⬝ᵥ xs + (expectedRecourse P pb xs).toReal ≤
      pb.c ⬝ᵥ x + (expectedRecourse P pb x).toReal := by
    intro x hx1 hx2
    have h := hopt.2 x hx1
    unfold depObjective at h
    rw [hcoe xs hxs2, hcoe x hx2, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact h
  have hsplit : ∀ v : Fin n1 → ℝ, (∀ x ∈ K1, x ∈ K2 → v ⬝ᵥ (x - xs) ≤ 0) →
      ∃ v1 v2 : Fin n1 → ℝ, v = v1 + v2 ∧ (∀ x ∈ K1, v1 ⬝ᵥ (x - xs) ≤ 0) ∧
        (∀ x ∈ K2, v2 ⬝ᵥ (x - xs) ≤ 0) := by
    intro v hv
    rcases hR with ⟨x0, hx01, hx0r⟩ | hpoly | hsub
    · exact P2MKKT.split_ri pb.A pb.b K2 hconv.1 x0 hx01 hx0r xs hxs hxs2 v hv
    · exact P2MKKT.split_poly pb.A pb.b K2 hpoly xs hxs hxs2 v hv
    · exact P2MKKT.split_sub K1 K2 hsub xs v hv
  obtain ⟨ζ, h1, h2⟩ := P2MKKT.abstract_kkt K1 K2 (P2MKKT.K1_convex pb.A pb.b) _ hconv L hL
    pb.c xs hxs hxs2 hopt' hsplit
  exact ⟨ζ, ne_of_lt hxs2, h1, h2⟩

theorem kkt9_of_6a {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (h6 : Six Ω P pb)
    (hfin : HasFiniteOptimalValue P pb)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b) :
    ((∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
          -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) →
        IsOptimalDEP P pb xs) ∧
      (((firstStageSet pb.A pb.b ∩ intrinsicInterior ℝ (secondStageFeasSet P pb)).Nonempty ∨
          IsPolyhedralSet (secondStageFeasSet P pb) ∨
          firstStageSet pb.A pb.b ⊆ secondStageFeasSet P pb) →
        IsOptimalDEP P pb xs →
          ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
            -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) := by
  refine ⟨fun h => suff9 P pb xs hxs h, fun hR hopt => ?_⟩
  obtain ⟨ζ, hfinx, hsub, hK1⟩ := coc_of_6a P pb h6 hfin xs hxs hR hopt
  have hmem : pb.c + ζ ∈ {η : Fin n1 → ℝ | ∀ x ∈ firstStageSet pb.A pb.b, 0 ≤ η ⬝ᵥ (x - xs)} := hK1
  rw [nc_K1 pb.A pb.b xs hxs] at hmem
  obtain ⟨lam, mu, hmu, hmux, heq⟩ := hmem
  refine ⟨lam, mu, hmu, hmux, ?_⟩
  have hζ : -pb.c + pb.Aᵀ *ᵥ lam + mu = ζ := by
    rw [add_assoc, ← heq]; abel
  rw [hζ]
  refine ⟨(expectedRecourse P pb xs).toReal, ?_, fun w => ?_⟩
  · exact (EReal.coe_toReal hfinx (h6.1 xs (by
      show expectedRecourse P pb xs < ⊤
      exact lt_top_iff_ne_top.2 hfinx))).symm
  · by_cases hw : w ∈ secondStageFeasSet P pb
    · have := hsub w hw
      rw [← EReal.coe_toReal (ne_of_lt hw) (h6.1 w hw)]
      exact EReal.coe_le_coe_iff.2 this
    · have : expectedRecourse P pb w = ⊤ := not_lt_top_iff.1 hw
      rw [this]; exact le_top

end KKT9

open MeasureTheory Matrix StochasticProg.RecourseKKT in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (hmom : FiniteSecondMoments P pb) (hnn : RecourseNotNegInf P pb)
    (hfin : HasFiniteOptimalValue P pb)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b) :
    ((∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
          -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) →
        IsOptimalDEP P pb xs) ∧
      (((firstStageSet pb.A pb.b ∩ intrinsicInterior ℝ (secondStageFeasSet P pb)).Nonempty ∨
          IsPolyhedralSet (secondStageFeasSet P pb) ∨
          firstStageSet pb.A pb.b ⊆ secondStageFeasSet P pb) →
        IsOptimalDEP P pb xs →
          ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
            -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) := by
  exact kkt9_of_6a P pb (P2MSix.six P pb hmom hnn) hfin xs hxs
