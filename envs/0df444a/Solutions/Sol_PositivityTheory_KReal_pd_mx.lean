-- Prove2me | solution 1 for PositivityTheory.KReal.pd_mx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:19.056316+00:00
-- url     : https://prove2.me/submissions/7cbc9669-5411-469b-ac15-774e9985606a

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
    ((pderiv a).toLinearMap * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * (pderiv a).toLinearMap + if a = b then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases h : a = b
  · subst h
    simp [Derivation.leibniz]
  · simp [Derivation.leibniz, h, pderiv_X_of_ne (Ne.symm h)]
end PositivityTheory.KReal
