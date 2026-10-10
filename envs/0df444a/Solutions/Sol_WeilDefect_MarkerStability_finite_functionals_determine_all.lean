-- Prove2me | solution 1 for WeilDefect.MarkerStability.finite_functionals_determine_all
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:25:59.553752+00:00
-- url     : https://prove2.me/submissions/91bb361c-41c6-4f3c-b7b6-499ea278764a

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
theorem solution
    {V Ω : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (r : Ω → Module.Dual ℂ V) :
    ∃ G : Finset Ω, G.card ≤ Module.finrank ℂ V ∧
      ∀ v : V, (∀ ρ ∈ G, r ρ v = 0) ↔ ∀ ρ : Ω, r ρ v = 0 := by
  obtain ⟨f, hf, hs, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range r)
  choose a ha using hf
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · calc
      (Finset.univ.image a).card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℂ (Submodule.span ℂ (Set.range r)) := by simp
      _ ≤ Module.finrank ℂ (Module.Dual ℂ V) := Submodule.finrank_le _
      _ = Module.finrank ℂ V := Subspace.dual_finrank_eq
  · intro v
    constructor
    · intro h
      let L : Module.Dual ℂ V →ₗ[ℂ] ℂ :=
        { toFun := fun q => q v
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hspan : Submodule.span ℂ (Set.range f) ≤ LinearMap.ker L := by
        apply Submodule.span_le.mpr
        rintro q ⟨i, rfl⟩
        change f i v = 0
        rw [← ha i]
        exact h (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      rw [hs] at hspan
      intro ρ
      exact hspan (Submodule.subset_span ⟨ρ, rfl⟩)
    · intro h ρ _
      exact h ρ
