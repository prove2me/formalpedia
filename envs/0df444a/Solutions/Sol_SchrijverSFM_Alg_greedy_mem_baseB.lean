-- Prove2me | solution 1 for SchrijverSFM.Alg.greedy_mem_baseB
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:15:08.535378+00:00
-- url     : https://prove2.me/submissions/9a35f0ad-a550-4709-9c18-de1f1d2bd97d

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

open SchrijverSFM.Alg NonmonotoneSubmod.Shared Finset

private theorem marginal {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (X Y : Finset (Fin n)) (hXY : X ⊆ Y) (v : Fin n) (hv : v ∉ Y) :
    f (insert v Y) - f Y ≤ f (insert v X) - f X := by
  have hu : insert v X ∪ Y = insert v Y := by
    ext a
    simp only [mem_union, mem_insert]
    constructor
    · rintro ((rfl | ha) | ha)
      · exact Or.inl rfl
      · exact Or.inr (hXY ha)
      · exact Or.inr ha
    · rintro (rfl | ha)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ha
  have hi : insert v X ∩ Y = X := by
    ext a
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | ha, hy⟩
      · exact False.elim (hv hy)
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hXY ha⟩
  have h := hsub (insert v X) Y
  rw [hu, hi] at h
  linarith

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (σ : Equiv.Perm (Fin n)) :
    (∀ U : Finset (Fin n), IsLowerIdeal σ U → xsum (greedy f σ) U = f U) ∧
      greedy f σ ∈ baseB f := by
  classical
  have all (U : Finset (Fin n)) : xsum (greedy f σ) U ≤ f U ∧
      (IsLowerIdeal σ U → xsum (greedy f σ) U = f U) := by
    refine Finset.strongInductionOn U ?_
    intro U ih
    by_cases hU : U = ∅
    · subst U
      simp [xsum, hf0]
    obtain ⟨v, hv, hmax⟩ := exists_max_image U σ (nonempty_iff_ne_empty.mpr hU)
    let V := U.erase v
    have hvV : v ∉ V := by simp [V]
    have hVU : V ⊂ U := erase_ssubset hv
    have hVb : V ⊆ before σ v := by
      intro x hx
      have hxU := (mem_erase.mp hx).2
      have hne := (mem_erase.mp hx).1
      have hle := hmax x hxU
      have hneq : σ x ≠ σ v := fun h => hne (σ.injective h)
      exact mem_filter.mpr ⟨mem_univ _, lt_of_le_of_ne hle hneq⟩
    have hvb : v ∉ before σ v := by simp [before]
    have hrec := ih V hVU
    have hins : insert v V = U := insert_erase hv
    have hsum : xsum (greedy f σ) U = greedy f σ v + xsum (greedy f σ) V := by
      rw [← hins]
      exact sum_insert hvV
    have hmar := marginal f hsub V (before σ v) hVb v hvb
    constructor
    · rw [hsum]
      change f (insert v (before σ v)) - f (before σ v) + xsum (greedy f σ) V ≤ f U
      rw [hins] at hmar
      linarith [hrec.1]
    · intro hideal
      have hVe : V = before σ v := by
        apply Subset.antisymm hVb
        intro x hx
        have hlt := (mem_filter.mp hx).2
        exact mem_erase.mpr ⟨fun h => by subst x; exact lt_irrefl _ hlt, hideal v hv x hlt⟩
      have hVi : IsLowerIdeal σ V := by
        intro u hu w hw
        have hub := (mem_filter.mp (hVb hu)).2
        rw [hVe]
        exact mem_filter.mpr ⟨mem_univ _, hw.trans hub⟩
      rw [hsum, hrec.2 hVi]
      unfold greedy
      rw [← hVe, hins]
      ring
  have hfull : IsLowerIdeal σ (univ : Finset (Fin n)) := by
    intro u hu w hw
    exact mem_univ _
  exact ⟨fun U hU => (all U).2 hU, fun U => (all U).1, (all univ).2 hfull⟩

#print axioms solution
