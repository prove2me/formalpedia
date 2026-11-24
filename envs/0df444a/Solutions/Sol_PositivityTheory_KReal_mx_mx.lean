-- Prove2me | solution 1 for PositivityTheory.KReal.mx_mx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:21.45488+00:00
-- url     : https://prove2.me/submissions/da1dce4c-2a85-4cce-9951-efa691698d7f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {σ : Type*} [DecidableEq σ]
namespace PositivityTheory.KReal
theorem _root_.solution (a b : σ) :
    (LinearMap.mulLeft ℂ (X a) * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * LinearMap.mulLeft ℂ (X a) := by
  refine LinearMap.ext fun P => ?_
  simp [mul_left_comm]
end PositivityTheory.KReal
