-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSubmodule_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:56:46.14018+00:00
-- url     : https://prove2.me/submissions/b88cb84e-be23-46a6-bca6-5e7ec4e0db0e

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L335-L338
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
theorem solution :
    (0 : ElementaryLieGroup m n r F → ℂ) ∈
      {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
        ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)} := by
  constructor
  · exact fun a b ↦ contDiff_const
  · intro i
    simp [elementarySchwartzBound, elementaryPartial, iteratedFDeriv_fun_zero]
