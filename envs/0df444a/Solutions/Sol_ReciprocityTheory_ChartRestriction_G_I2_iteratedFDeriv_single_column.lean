-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.iteratedFDeriv_single_column
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:54.92621+00:00
-- url     : https://prove2.me/submissions/ba0d59ce-a8f5-46d0-9893-7c67f9c4b55d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {c : ℕ} {g : V → ℂ}
    (hg : ContDiff ℂ c g) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun w : Fin 1 → V => g (w 0)) 0 (fun k _ => x k) = iteratedFDeriv ℂ c g 0 x := by
  let pr : (Fin 1 → V) →L[ℂ] V := ContinuousLinearMap.proj 0
  have := pr.iteratedFDeriv_comp_right hg (0 : Fin 1 → V) le_rfl
  have h2 := congrArg (fun M => M (fun k _ => x k)) this
  simp only [pr, ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.I2
