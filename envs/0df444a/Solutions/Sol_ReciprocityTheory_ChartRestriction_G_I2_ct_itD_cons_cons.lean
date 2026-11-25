-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_itD_cons_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:20.956201+00:00
-- url     : https://prove2.me/submissions/3f961a7d-2c19-49b0-92d9-1bda7913c99b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_contDiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_cons


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
theorem _root_.solution {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (a b : W) (l : List W) (z : W) :
    itD f (a :: b :: l) z = fderiv ℂ (fderiv ℂ (fun y => itD f l y)) z a b := by
  have hg := ct_itD_contDiff hf l
  have h1 := contDiff_infty_iff_fderiv.1 hg
  have h2 := (contDiff_infty_iff_fderiv.1 h1.2).1
  rw [itD_cons hf]
  have hc : (fun y => itD f (b :: l) y) =
      (ContinuousLinearMap.apply ℂ ℂ b) ∘ fderiv ℂ (fun y => itD f l y) := by
    funext y
    exact itD_cons hf b l y
  rw [hc, fderiv_comp z (ContinuousLinearMap.differentiableAt _) (h2 z), ContinuousLinearMap.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.G.I2
