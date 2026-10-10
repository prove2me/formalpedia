-- Prove2me | solution 1 for WeilDefect.MarkerStability.finite_sampling_rows_determine_all
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:05:32.09589+00:00
-- url     : https://prove2.me/submissions/9eb50224-3aaf-4da5-8d9d-288f85839665

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
open Matrix
open scoped BigOperators Classical
noncomputable section
theorem solution
    {I Ω : Type*} [Fintype I] (r : Ω → (I → ℂ)) :
    ∃ G : Finset Ω, G.card ≤ Fintype.card I ∧
      ∀ c : I → ℂ, (∀ ρ ∈ G, r ρ ⬝ᵥ c = 0) ↔ ∀ ρ : Ω, r ρ ⬝ᵥ c = 0 := by
  obtain ⟨f, hf, hs, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range r)
  choose a ha using hf
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · calc
      (Finset.univ.image a).card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℂ (Submodule.span ℂ (Set.range r)) := by simp
      _ ≤ Fintype.card I := by
        simpa only [Module.finrank_pi] using
          (Submodule.finrank_le (Submodule.span ℂ (Set.range r)))
  · intro c
    constructor
    · intro h
      let L : (I → ℂ) →ₗ[ℂ] ℂ :=
        { toFun := fun v => v ⬝ᵥ c
          map_add' := fun _ _ => add_dotProduct _ _ _
          map_smul' := fun _ _ => by simp only [smul_dotProduct, RingHom.id_apply] }
      have hspan : Submodule.span ℂ (Set.range f) ≤ LinearMap.ker L := by
        apply Submodule.span_le.mpr
        rintro v ⟨i, rfl⟩
        change f i ⬝ᵥ c = 0
        rw [← ha i]
        exact h (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      rw [hs] at hspan
      intro ρ
      exact hspan (Submodule.subset_span ⟨ρ, rfl⟩)
    · intro h ρ _
      exact h ρ
