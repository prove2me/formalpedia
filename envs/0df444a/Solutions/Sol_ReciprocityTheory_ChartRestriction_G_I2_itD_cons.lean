-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.itD_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:36.015846+00:00
-- url     : https://prove2.me/submissions/85e440e9-1923-4a91-a6c5-f61fdb176a73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (e : W) (l : List W) (z : W) :
    itD f (e :: l) z = fderiv ℂ (fun y => itD f l y) z e := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  show iteratedFDeriv ℂ (l.length + 1) f z (fun j => (e :: l).get j) = _
  rw [iteratedFDeriv_succ_apply_left]
  have hc : (fun y => itD f l y) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ (fun j => l.get j)) ∘
        iteratedFDeriv ℂ l.length f := rfl
  rw [hc, fderiv_comp z (ContinuousLinearMap.differentiableAt _) (hD z), ContinuousLinearMap.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.G.I2
