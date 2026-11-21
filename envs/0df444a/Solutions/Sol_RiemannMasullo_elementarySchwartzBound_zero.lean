-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzBound_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:42:51.229004+00:00
-- url     : https://prove2.me/submissions/07203a54-13c9-4022-b789-2ec497723228

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L325-L327
import Theorems.Thm_RiemannMasullo_elementaryCover_surjective
import Theorems.Thm_RiemannMasullo_elementaryPartial_zero
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution (f : ElementaryLieGroup m n r F → ℂ) :
    elementarySchwartzBound f (0, 0, 0, 0) =
      ⨆ g, (‖f g‖₊ : ℝ≥0∞) := by
  classical
  simp only [elementarySchwartzBound, Pi.zero_apply, pow_zero, Finset.prod_const_one,
    one_mul, elementaryPartial_zero]
  apply le_antisymm
  · exact iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦
      le_iSup (fun g ↦ (‖f g‖₊ : ℝ≥0∞)) (elementaryCover xt a b)
  · apply iSup_le
    rintro ⟨x,z,a,b⟩
    obtain ⟨t, ht⟩ := elementaryCover_surjective a b x z
    rw [← ht]
    exact le_iSup_of_le (x, t) (le_iSup_of_le a (le_iSup_of_le b le_rfl))
