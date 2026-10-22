-- Prove2me | solution 1 for ProcureAssort.Hotelling.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:25:21.603128+00:00
-- url     : https://prove2.me/submissions/66921741-850b-42ad-b608-0bc02476dce6

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting
import Theorems.Thm_ProcureAssort_Hotelling_proposition_3_1
import Theorems.Thm_ProcureAssort_Hotelling_proposition_3_2
import Theorems.Thm_ProcureAssort_Hotelling_corollary_4_1
import Theorems.Thm_ProcureAssort_Hotelling_lemma_F_1
import Theorems.Thm_ProcureAssort_Hotelling_step_1
import Theorems.Thm_ProcureAssort_Hotelling_step_2
import Theorems.Thm_ProcureAssort_Hotelling_eq_M_implies_demand

open ProcureAssort.Hotelling

theorem solution
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (h1 : ∃ θ : Profile Θ, ∀ i : Fin n, ∀ h : i.val + 1 < n,
      |virtualCost Θ f ⟨i.val + 1, h⟩ (θ ⟨i.val + 1, h⟩) - virtualCost Θ f i (θ i)|
        ≤ δ * (ℓ ⟨i.val + 1, h⟩ - ℓ i) / 4)
    (h2 : ∀ i, 3 ≤ (Θ i).card ∧ ∀ a ∈ Θ i, ∀ b ∈ Θ i, a < b → (∀ c ∈ Θ i, ¬ (a < c ∧ c < b)) →
      virtualCost Θ f i b - virtualCost Θ f i a ≤ δ * cstar ℓ hn / 8) :
    optDecLin Θ f (hotGCS ℓ δ) (simplex n) = optCent Θ f (hotGCS ℓ δ) (simplex n) := by
  classical
  set x := xstar Θ f ℓ δ with hxdef
  set t := tstar Θ (xstar Θ f ℓ δ) with htdef
  set Q := activeSet Θ f ℓ δ with hQdef
  obtain ⟨hfeas, hc1, hc2, hc3, -⟩ :=
    proposition_3_2 n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ
  have hX : ∀ y ∈ simplex n, ∀ i, 0 ≤ y i := fun y hy i => hy.1 i
  have hopt := (proposition_3_1 Θ hΘ f hf0 hf1 hreg (hotGCS ℓ δ) (simplex n) hX x t hc1 hc2 hc3).2
  have hxnn : ∀ θ i, 0 ≤ x θ i := fun θ i => (hc1 θ).1.1 i
  -- the linear system
  let ι := (Profile Θ × Fin n) ⊕ ((i : Fin n) × ↥(Θ i))
  let κ := Profile Θ × Fin n
  let M1 : (Profile Θ × Fin n) → κ → ℝ := fun r col =>
    if col.1 = r.1 then pathA (Q r.1) r.2 col.2 else 0
  let M2 : ((i : Fin n) × ↥(Θ i)) → κ → ℝ := fun r col =>
    if col.2 = r.1 ∧ ((col.1 r.1 : ℝ) = (r.2 : ℝ)) then probOthers f r.1 col.1 * x col.1 r.1 else 0
  let M : Matrix ι κ ℝ := Matrix.of fun r => Sum.elim M1 M2 r
  let m1 : (Profile Θ × Fin n) → ℝ := fun r => ∑ j ∈ Q r.1, pathA (Q r.1) r.2 j * vvec Θ f r.1 j
  let m2 : ((i : Fin n) × ↥(Θ i)) → ℝ := fun r => interim f (fun θ => t θ r.1) r.1 r.2
  let m : ι → ℝ := fun r => Sum.elim m1 m2 r
  have hMv1 : ∀ (p : κ → ℝ) (θ : Profile Θ) (i : Fin n),
      Matrix.mulVec M p (Sum.inl (θ, i)) = ∑ j, pathA (Q θ) i j * p (θ, j) := by
    intro p θ i
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single θ]
    · simp [M, M1]
    · intro θ' _ hθ'
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [M, M1, hθ']
    · simp
  have hMv2 : ∀ (p : κ → ℝ) (i : Fin n) (c : ↥(Θ i)),
      Matrix.mulVec M p (Sum.inr ⟨i, c⟩) = interim f (fun θ => p (θ, i) * x θ i) i c := by
    intro p i c
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type]
    unfold interim
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [M, M2, Matrix.of_apply, Sum.elim_inr, true_and]
      split_ifs <;> ring
    · intro j _ hj
      simp [M, M2, hj]
    · simp
  have hvM : ∀ (y : ι → ℝ) (θ : Profile Θ) (j : Fin n),
      Matrix.vecMul y M (θ, j) = ∑ i, y (Sum.inl (θ, i)) * pathA (Q θ) i j +
        y (Sum.inr ⟨j, θ j⟩) * (probOthers f j θ * x θ j) := by
    intro y θ j
    simp only [Matrix.vecMul, dotProduct]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma]
    congr 1
    · rw [Finset.sum_eq_single θ]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [M, M1]
      · intro θ' _ hθ'
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [M, M1, Ne.symm hθ']
      · simp
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single (θ j)]
        · simp [M, M2]
        · intro c _ hc
          have : ¬ ((θ j : ℝ) = (c : ℝ)) := fun h => hc (Subtype.ext h).symm
          simp only [M, M2, Matrix.of_apply, Sum.elim_inr, true_and, if_neg this, mul_zero]
        · simp
      · intro i _ hij
        refine Finset.sum_eq_zero fun c _ => ?_
        simp [M, M2, Ne.symm hij]
      · simp
  have hpathA_out : ∀ (S : Finset (Fin n)) (i j : Fin n), (i ∉ S ∨ j ∉ S) → pathA S i j = 0 := by
    intro S i j h
    unfold pathA
    rw [if_neg]
    tauto
  have hcons : ∃ p : κ → ℝ, Matrix.mulVec M p = m := by
    rw [lemma_F_1]
    intro y hy
    set a : Profile Θ → Fin n → ℝ := fun θ i => y (Sum.inl (θ, i)) with ha
    set b : Fin n → ℝ → ℝ := fun i c => if h : c ∈ Θ i then y (Sum.inr ⟨i, ⟨c, h⟩⟩) else 0
      with hb
    have hcol : ∀ (θ : Profile Θ) (j : Fin n),
        (∑ i, a θ i * pathA (Q θ) i j) + b j (θ j) * (probOthers f j θ * x θ j) = 0 := by
      intro θ j
      have := congrFun hy (θ, j)
      rw [hvM] at this
      simpa [ha, hb] using this
    have h14 : ∀ θ : Profile Θ, ∀ j ∈ Q θ,
        (∑ i ∈ Q θ, a θ i * pathA (Q θ) i j) + b j (θ j) * probOthers f j θ * x θ j = 0 := by
      intro θ j hj
      have := hcol θ j
      rw [← Finset.sum_subset (Finset.subset_univ (Q θ))] at this
      · rw [← this]; ring
      · intro i _ hi
        rw [hpathA_out _ _ _ (Or.inl hi), mul_zero]
    have hb0 := step_1 n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ h1 h2 a b h14
    have hbx : ∀ (θ : Profile Θ) (j : Fin n), b j (θ j) * x θ j = 0 := by
      intro θ j
      rcases (hxnn θ j).lt_or_eq with h | h
      · rw [hb0 j _ (θ j).2 ⟨θ, rfl, h⟩, zero_mul]
      · rw [← h, mul_zero]
    have h14' : ∀ θ : Profile Θ, ∀ j ∈ Q θ, ∑ i ∈ Q θ, a θ i * pathA (Q θ) i j = 0 := by
      intro θ j hj
      have := h14 θ j hj
      have h0 : b j (θ j) * probOthers f j θ * x θ j = 0 := by
        rw [mul_right_comm, hbx θ j, zero_mul]
      linarith
    have hs2 := step_2 n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ a h14'
    -- dot product
    simp only [dotProduct]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma]
    have hA : ∑ θ : Profile Θ, ∑ i : Fin n, y (Sum.inl (θ, i)) * m (Sum.inl (θ, i)) = 0 := by
      rw [← hs2]
      refine Finset.sum_congr rfl fun θ _ => ?_
      symm
      apply Finset.sum_subset (Finset.subset_univ (Q θ))
      intro i _ hi
      show _ * ∑ j ∈ Q θ, pathA (Q θ) i j * vvec Θ f θ j = 0
      rw [Finset.sum_eq_zero fun j _ => by rw [hpathA_out _ _ _ (Or.inl hi), zero_mul], mul_zero]
    have hB : ∑ i : Fin n, ∑ c : ↥(Θ i), y (Sum.inr ⟨i, c⟩) * m (Sum.inr ⟨i, c⟩) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun c _ => ?_
      by_cases hpos : ∃ θ : Profile Θ, (θ i : ℝ) = c ∧ 0 < x θ i
      · have := hb0 i c c.2 hpos
        simp only [hb, dif_pos c.2] at this
        rw [this, zero_mul]
      · push Not at hpos
        have hzero : ∀ θ : Profile Θ, (θ i : ℝ) = c → x θ i = 0 :=
          fun θ h => le_antisymm (hpos θ h) (hxnn θ i)
        have hXnn : ∀ d, 0 ≤ interim f (fun θ => x θ i) i d := by
          intro d
          unfold interim probOthers
          refine Finset.sum_nonneg fun θ _ => ?_
          split_ifs
          · exact mul_nonneg (Finset.prod_nonneg fun k _ => (hf0 k _ (θ k).2).le) (hxnn θ i)
          · exact le_rfl
        have hXc : interim f (fun θ => x θ i) i c = 0 := by
          unfold interim
          refine Finset.sum_eq_zero fun θ _ => ?_
          split_ifs with h
          · simp only; rw [hzero θ h, mul_zero]
          · rfl
        have hXb : ∀ d ∈ Θ i, (c : ℝ) ≤ d → interim f (fun θ => x θ i) i d = 0 := by
          intro d hd hcd
          exact le_antisymm (hXc ▸ hc2 i c c.2 d hd hcd) (hXnn d)
        show _ * interim f (fun θ => t θ i) i c = 0
        rw [hc3 i c c.2, hXc, Finset.sum_eq_zero fun d hd => by
          rw [Finset.mem_filter] at hd
          rw [hXb d hd.1 hd.2.le, mul_zero]]
        ring
    rw [hA, hB, add_zero]
  obtain ⟨p, hp⟩ := hcons
  let P : Profile Θ → Fin n → ℝ := fun θ j => p (θ, j)
  have hrow1 : ∀ (θ : Profile Θ) (i : Fin n),
      ∑ j, pathA (Q θ) i j * P θ j = ∑ j ∈ Q θ, pathA (Q θ) i j * vvec Θ f θ j := by
    intro θ i
    have := congrFun hp (Sum.inl (θ, i))
    rw [hMv1] at this
    exact this
  have hM : ∀ θ : Profile Θ, ∀ i ∈ Q θ,
      ∑ j ∈ Q θ, pathA (Q θ) i j * P θ j = ∑ j ∈ Q θ, pathA (Q θ) i j * vvec Θ f θ j := by
    intro θ i _
    rw [← hrow1 θ i]
    apply Finset.sum_subset (Finset.subset_univ (Q θ))
    intro j _ hj
    rw [hpathA_out _ _ _ (Or.inr hj), zero_mul]
  have h10 : ∀ θ, IsDemand (hotGCS ℓ δ) (simplex n)
      (Finset.univ.filter (fun i => 0 < x θ i)) (P θ) (x θ) := fun θ =>
    eq_M_implies_demand n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ θ (P θ) (hM θ)
  have h11 : ∀ i, ∀ c ∈ Θ i,
      interim f (fun θ => P θ i * x θ i) i c = interim f (fun θ => t θ i) i c := by
    intro i c hc
    have := congrFun hp (Sum.inr ⟨i, ⟨c, hc⟩⟩)
    rw [hMv2] at this
    exact this
  exact (corollary_4_1 Θ hΘ f hf0 hf1 hreg (hotGCS ℓ δ) (simplex n) x t hfeas hopt P h10 h11).2.2
