-- Prove2me | solution 1 for PCLAssort.lemma_6_ip_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:46:32.013738+00:00
-- url     : https://prove2.me/submissions/55fad3a1-d623-4946-a2a1-fb8715a123b6

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_DownwardClosed
import Definitions.Def_PCLAssort_ip1Value
import Definitions.Def_PCLAssort_ip2Value
import Definitions.Def_PCLAssort_constrDicutValue
import Definitions.Def_PCLAssort_pclWeight
import Definitions.Def_PCLAssort_tildeEdges

namespace PCLAssort.Aux_PC

open PCLAssort

theorem rpow_id {v γ : ℝ} (hv : 0 ≤ v) (hγ0 : 0 < γ) :
    v ^ (1 / γ) / (v ^ (1 / γ)) ^ (1 - γ) = v := by
  rcases hv.lt_or_eq with hpos | hzero
  · rw [← Real.rpow_mul hv, ← Real.rpow_sub hpos]
    have : 1 / γ - 1 / γ * (1 - γ) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  · subst hzero
    rw [Real.zero_rpow (by positivity), zero_div]

theorem rpow_bound {v u γ : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    0 ≤ v ^ (1 / γ) / (v ^ (1 / γ) + u ^ (1 / γ)) ^ (1 - γ) ∧
      v ^ (1 / γ) / (v ^ (1 / γ) + u ^ (1 / γ)) ^ (1 - γ) ≤ v := by
  have hva : 0 ≤ v ^ (1 / γ) := Real.rpow_nonneg hv _
  have hua : 0 ≤ u ^ (1 / γ) := Real.rpow_nonneg hu _
  refine ⟨div_nonneg hva (Real.rpow_nonneg (by linarith) _), ?_⟩
  rcases hv.lt_or_eq with hpos | hzero
  · have hvapos : 0 < v ^ (1 / γ) := Real.rpow_pos_of_pos hpos _
    have hden : (v ^ (1 / γ)) ^ (1 - γ) ≤ (v ^ (1 / γ) + u ^ (1 / γ)) ^ (1 - γ) :=
      Real.rpow_le_rpow hva (by linarith) (by linarith)
    have hden0 : 0 < (v ^ (1 / γ)) ^ (1 - γ) := Real.rpow_pos_of_pos hvapos _
    calc v ^ (1 / γ) / (v ^ (1 / γ) + u ^ (1 / γ)) ^ (1 - γ)
        ≤ v ^ (1 / γ) / (v ^ (1 / γ)) ^ (1 - γ) := div_le_div_of_nonneg_left hva hden0 hden
      _ = v := rpow_id hv hγ0
  · subst hzero
    rw [Real.zero_rpow (by positivity), zero_div]

/-- the share is `(r p - z)` times a factor in `[0, v p]` -/
theorem xi_split {n : ℕ} (I : PCLInstance n) (z : ℝ) (k l : Fin n) (hkl : k ≠ l) (p : Fin n)
    (hp : p = k ∨ p = l) :
    ∃ q, 0 ≤ q ∧ q ≤ I.v p ∧ xiShare I z k l p = (I.r p - z) * q := by
  have hγ0 := I.γ_pos k l hkl
  have hγ1 := I.γ_le_one k l hkl
  rcases hp with rfl | rfl
  · obtain ⟨h1, h2⟩ := rpow_bound (I.v_nonneg p) (I.v_nonneg l) hγ0 hγ1
    exact ⟨_, h1, h2, by unfold xiShare; ring⟩
  · obtain ⟨h1, h2⟩ := rpow_bound (I.v_nonneg p) (I.v_nonneg k) hγ0 hγ1
    refine ⟨_, h1, h2, ?_⟩
    unfold xiShare
    rw [add_comm (I.v k ^ (1 / I.γ k p))]
    ring

theorem weight_sign {n : ℕ} (I : PCLInstance n) (z : ℝ) (i : Fin n) (o : Option (Fin n))
    (ho : o ≠ some i) :
    (z ≤ I.r i → 0 ≤ pclWeight I z (some i, o)) ∧ (I.r i ≤ z → pclWeight I z (some i, o) ≤ 0) := by
  cases o with
  | none =>
    simp only [pclWeight]
    have hterm : ∀ k ∈ Finset.univ.erase i, ∃ q, 0 ≤ q ∧
        xiShare I z i k i + xiShare I z k i i = (I.r i - z) * q := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      obtain ⟨q1, h1, _, e1⟩ := xi_split I z i k (Ne.symm hki) i (Or.inl rfl)
      obtain ⟨q2, h2, _, e2⟩ := xi_split I z k i hki i (Or.inr rfl)
      exact ⟨q1 + q2, by linarith, by rw [e1, e2]; ring⟩
    constructor
    · intro hz
      apply Finset.sum_nonneg
      intro k hk
      obtain ⟨q, hq, e⟩ := hterm k hk
      rw [e]; exact mul_nonneg (by linarith) hq
    · intro hz
      apply Finset.sum_nonpos
      intro k hk
      obtain ⟨q, hq, e⟩ := hterm k hk
      rw [e]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
  | some j =>
    have hij : i ≠ j := fun h => ho (by rw [h])
    simp only [pclWeight, if_neg hij]
    obtain ⟨q1, h1, h1', e1⟩ := xi_split I z i j hij i (Or.inl rfl)
    obtain ⟨q2, h2, h2', e2⟩ := xi_split I z j i (Ne.symm hij) i (Or.inr rfl)
    rw [e1, e2]
    have hform : 2 * (I.v i * (I.r i - z)) - (I.r i - z) * q1 - (I.r i - z) * q2 =
        (I.r i - z) * (2 * I.v i - q1 - q2) := by ring
    rw [hform]
    have hb : 0 ≤ 2 * I.v i - q1 - q2 := by linarith
    constructor
    · intro hz; exact mul_nonneg (by linarith) hb
    · intro hz; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hb

/-- allowed edges of a set `S` -/
def allowed {n : ℕ} (S : Finset (Fin n)) : Finset (Option (Fin n) × Option (Fin n)) :=
  (pclEdges n).filter fun e => e.1 ∈ S.image some ∧ e.2 ∉ S.image some

theorem sum_allowed {n : ℕ} (S : Finset (Fin n)) (w : Option (Fin n) × Option (Fin n) → ℝ) :
    ∑ e ∈ allowed S, w e =
      ∑ i, if i ∈ S then (w (some i, none) + ∑ j, if j ∈ S then 0 else w (some i, some j)) else 0 := by
  classical
  unfold allowed pclEdges
  rw [Finset.filter_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_option]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    congr 1
    · simp [hi, Finset.mem_image]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · simp [hj, Finset.mem_image]
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp [hi, hj, hij, Finset.mem_image]
  · rw [if_neg hi]
    simp [hi, Finset.mem_image]

theorem ip1_eq {n : ℕ} (I : PCLInstance n) (z : ℝ) (S : Finset (Fin n)) :
    ip1Objective I z S = ∑ e ∈ allowed S, pclWeight I z e := by
  classical
  rw [sum_allowed]
  set c : Fin n → ℝ := fun i => I.v i * (I.r i - z) with hc
  set ξ : Fin n → Fin n → Fin n → ℝ := fun k l p => xiShare I z k l p with hξ
  -- the two halves
  set Pf : Fin n → Fin n → ℝ := fun i j =>
    if i ≠ j then (if i ∈ S then (if j ∈ S then ξ i j i else c i) else 0) else 0 with hPf
  set Rf : Fin n → Fin n → ℝ := fun i j =>
    if i ≠ j then (if i ∈ S then (if j ∈ S then ξ j i i else c i) else 0) else 0 with hRf
  have hT : ip1Objective I z S = ∑ i, ∑ j, (Pf i j + Rf j i) := by
    unfold ip1Objective
    have hoff : (Finset.univ : Finset (Fin n)).offDiag =
        (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2) := by
      ext p
      simp [Finset.mem_offDiag]
    rw [hoff, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst hij
      simp [hPf, hRf]
    · have hji : j ≠ i := Ne.symm hij
      have hγ0 := I.γ_pos i j hij
      simp only [ne_eq, hij, not_false_eq_true, if_true]
      simp only [hPf, hRf, if_pos hij, if_pos hji, nestWeight]
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
      · simp only [hi, hj, if_true, mul_one, hξ, xiShare]
        rw [add_div]
      · simp only [hi, hj, if_true, if_false, mul_one, mul_zero, add_zero, hc]
        rw [mul_div_assoc, rpow_id (I.v_nonneg i) hγ0]
        ring
      · simp only [hi, hj, if_true, if_false, mul_one, mul_zero, zero_add, hc]
        rw [mul_div_assoc, rpow_id (I.v_nonneg j) hγ0]
        ring
      · simp [hi, hj]
  have hE : ∀ i, (if i ∈ S then (pclWeight I z (some i, none) +
      ∑ j, if j ∈ S then 0 else pclWeight I z (some i, some j)) else 0) =
      ∑ j, (Pf i j + Rf i j) := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      simp only [pclWeight]
      rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst hji
        simp [hPf, hRf, hi]
      · have hij : i ≠ j := Ne.symm hji
        by_cases hj : j ∈ S
        · simp [hPf, hRf, hi, hj, hij, hji, hξ]
        · simp [hPf, hRf, hi, hj, hij, hji, hξ, hc]
          ring
    · rw [if_neg hi]
      symm
      apply Finset.sum_eq_zero
      intro j _
      simp [hPf, hRf, hi]
  rw [hT, Finset.sum_congr rfl (fun i _ => hE i)]
  simp only [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end PCLAssort.Aux_PC

open PCLAssort PCLAssort.Aux_PC in
theorem solution {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n)))
    (hF : DownwardClosed F) :
    ∀ z : ℝ, ip1Value I F z = ip2Value I F z ∧
      ip2Value I F z = constrDicutValue (tildeEdges I z) (pclWeight I z) F := by
  classical
  intro z
  have hFne : Nonempty F := ⟨⟨∅, hF.1⟩⟩
  -- the edges of a set
  have hallowed_mem : ∀ S : Finset (Fin n), ∀ e ∈ allowed S,
      e.1 ∈ S.image some ∧ e.2 ∉ S.image some := by
    intro S e he
    exact (Finset.mem_filter.mp he).2
  set Qt := {q : Finset (Fin n) × Finset (Option (Fin n) × Option (Fin n)) //
      q.1 ∈ F ∧ q.2 ⊆ pclEdges n ∧ ∀ e ∈ q.2, e.1 ∈ q.1.image some ∧ e.2 ∉ q.1.image some}
  have hQne : Nonempty Qt := ⟨⟨(∅, ∅), hF.1, Finset.empty_subset _, by simp⟩⟩
  have hb1 : BddAbove (Set.range fun S : F => ip1Objective I z S.1) := (Set.finite_range _).bddAbove
  have hb2 : BddAbove (Set.range fun q : Qt => ∑ e ∈ q.1.2, pclWeight I z e) :=
    (Set.finite_range _).bddAbove
  have hb3 : BddAbove (Set.range fun S : F => cutValue (tildeEdges I z) (pclWeight I z) (S.1.image some)) :=
    (Set.finite_range _).bddAbove
  -- ip1 ≤ ip2
  have h12 : ip1Value I F z ≤ ip2Value I F z := by
    unfold ip1Value ip2Value
    apply ciSup_le
    intro S
    apply le_ciSup_of_le hb2 ⟨(S.1, allowed S.1), S.2, Finset.filter_subset _ _, hallowed_mem S.1⟩
    rw [ip1_eq]
  -- ip2 ≤ dicut
  have h23 : ip2Value I F z ≤ constrDicutValue (tildeEdges I z) (pclWeight I z) F := by
    unfold ip2Value constrDicutValue
    apply ciSup_le
    rintro ⟨⟨S, Q⟩, hS, hQ, hQe⟩
    apply le_ciSup_of_le hb3 ⟨S, hS⟩
    simp only [cutValue, tildeEdges]
    calc ∑ e ∈ Q, pclWeight I z e ≤ ∑ e ∈ Q.filter (fun e => 0 ≤ pclWeight I z e), pclWeight I z e := by
          rw [← Finset.sum_filter_add_sum_filter_not Q (fun e => 0 ≤ pclWeight I z e)]
          have : ∑ e ∈ Q.filter (fun e => ¬ 0 ≤ pclWeight I z e), pclWeight I z e ≤ 0 :=
            Finset.sum_nonpos fun e he => le_of_lt (not_le.mp (Finset.mem_filter.mp he).2)
          linarith
      _ ≤ ∑ e ∈ ((pclEdges n).filter (fun e => 0 ≤ pclWeight I z e)).filter
            (fun e => e.1 ∈ S.image some ∧ e.2 ∉ S.image some), pclWeight I z e := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            rw [Finset.mem_filter] at he
            rw [Finset.mem_filter, Finset.mem_filter]
            exact ⟨⟨hQ he.1, he.2⟩, hQe e he.1⟩
          · intro e he _
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  -- dicut ≤ ip1
  have h31 : constrDicutValue (tildeEdges I z) (pclWeight I z) F ≤ ip1Value I F z := by
    unfold constrDicutValue ip1Value
    apply ciSup_le
    rintro ⟨S, hS⟩
    set S' := S.filter (fun i => z ≤ I.r i) with hS'
    have hS'F : S' ∈ F := hF.2 S hS S' (Finset.filter_subset _ _)
    apply le_ciSup_of_le hb1 ⟨S', hS'F⟩
    simp only
    rw [ip1_eq]
    simp only [cutValue, tildeEdges]
    -- split the cut by the sign of the tail
    set X := ((pclEdges n).filter (fun e => 0 ≤ pclWeight I z e)).filter
      (fun e => e.1 ∈ S.image some ∧ e.2 ∉ S.image some) with hX
    have hzero : ∀ e ∈ X.filter (fun e => ¬ e.1 ∈ S'.image some), pclWeight I z e = 0 := by
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heX, hnot⟩ := he
      rw [hX, Finset.mem_filter, Finset.mem_filter] at heX
      obtain ⟨⟨hpcl, hnn⟩, hin, _⟩ := heX
      rw [Finset.mem_image] at hin
      obtain ⟨i, hiS, hie⟩ := hin
      have hri : I.r i < z := by
        by_contra h
        push_neg at h
        exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, h⟩, hie⟩)
      obtain ⟨e1, e2⟩ := e
      simp only at hie
      subst hie
      have hne : e2 ≠ some i := by
        intro h
        have := (Finset.mem_filter.mp hpcl).2.2
        simp only at this
        exact this h.symm
      have := (weight_sign I z i e2 hne).2 hri.le
      linarith
    rw [← Finset.sum_filter_add_sum_filter_not X (fun e => e.1 ∈ S'.image some),
      Finset.sum_eq_zero hzero, add_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heX, hin'⟩ := he
      rw [hX, Finset.mem_filter, Finset.mem_filter] at heX
      obtain ⟨⟨hpcl, _⟩, _, hout⟩ := heX
      unfold allowed
      rw [Finset.mem_filter]
      refine ⟨hpcl, hin', ?_⟩
      intro h
      apply hout
      rw [Finset.mem_image] at h ⊢
      obtain ⟨j, hj, hje⟩ := h
      exact ⟨j, (Finset.mem_filter.mp hj).1, hje⟩
    · intro e he _
      unfold allowed at he
      rw [Finset.mem_filter] at he
      obtain ⟨hpcl, hin, _⟩ := he
      rw [Finset.mem_image] at hin
      obtain ⟨i, hi, hie⟩ := hin
      obtain ⟨e1, e2⟩ := e
      simp only at hie
      subst hie
      have hne : e2 ≠ some i := by
        intro h
        have := (Finset.mem_filter.mp hpcl).2.2
        simp only at this
        exact this h.symm
      exact (weight_sign I z i e2 hne).1 (Finset.mem_filter.mp hi).2
  exact ⟨le_antisymm h12 (h23.trans h31), le_antisymm h23 (h31.trans h12)⟩
