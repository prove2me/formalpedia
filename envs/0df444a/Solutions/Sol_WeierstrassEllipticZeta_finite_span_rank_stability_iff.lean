-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_span_rank_stability_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:00:42.910311+00:00
-- url     : https://prove2.me/submissions/003d855e-de1a-49c1-9a68-9395c7b1bc19

import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

theorem solution
    (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι] (f : ι → V) (S B : Finset ι) :
    (∀ b ∈ B, f b ∈ Submodule.span K (f '' (S : Set ι))) ↔
      Module.finrank K (Submodule.span K (f '' ((S ∪ B : Finset ι) : Set ι))) =
        Module.finrank K (Submodule.span K (f '' (S : Set ι))) := by
  classical
  let U : Submodule K V := Submodule.span K (f '' (S : Set ι))
  let W : Submodule K V := Submodule.span K (f '' ((S ∪ B : Finset ι) : Set ι))
  have hle : U ≤ W := by
    apply Submodule.span_mono
    apply Set.image_mono
    intro i hi
    exact Finset.mem_union.mpr (Or.inl hi)
  constructor
  · intro h
    have hWU : W ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      rcases Finset.mem_union.mp hi with hi | hi
      · exact Submodule.subset_span ⟨i, hi, rfl⟩
      · exact h i hi
    exact congrArg (fun P : Submodule K V => Module.finrank K P) (le_antisymm hWU hle)
  · intro hrank
    let : FiniteDimensional K W :=
      FiniteDimensional.span_of_finite K ((S ∪ B).finite_toSet.image f)
    have heq : U = W := Submodule.eq_of_le_of_finrank_eq hle hrank.symm
    intro i hi
    change f i ∈ U
    rw [heq]
    exact Submodule.subset_span ⟨i, Finset.mem_union.mpr (Or.inr hi), rfl⟩
