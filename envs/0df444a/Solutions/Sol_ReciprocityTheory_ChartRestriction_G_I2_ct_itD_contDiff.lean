-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_itD_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:27:46.98692+00:00
-- url     : https://prove2.me/submissions/57f7ecd6-be31-404c-a307-d346d8b5f7d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (l : List W) :
    ContDiff ℂ (⊤ : ℕ∞) (fun y => itD f l y) := by
  unfold itD
  have h : ContDiff ℂ (⊤ : ℕ∞) (iteratedFDeriv ℂ l.length f) := by
    refine contDiff_infty.2 fun m => hf.iteratedFDeriv_right ?_
    first
      | exact_mod_cast (le_top : ((m + l.length : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.2 le_top
      | simp
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ _).contDiff.comp h
end ReciprocityTheory.ChartRestriction.G.I2
