-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.hasDerivAt_lin_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:59.665628+00:00
-- url     : https://prove2.me/submissions/6775ec33-37f6-471a-9ea4-9020e1640a24

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] F)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • X))) (L (NormedSpace.exp (t • X) * X)) t := by
  letI := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)
end PositivityTheory.ThKR.LL
