-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_fsLogReg_sub_110b7e07e698
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:14.397126+00:00
-- url     : https://prove2.me/submissions/9b0adbed-e170-4f47-a74f-1df3040f44c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution (h : HermNorm n) (u x : Fin n → ℂ) (hu : linEval u x ≠ 0)
    (hx : 0 < h.dualNorm x) :
    Tendsto (fun ε => fsLogReg h u ε x) (𝓝[>] 0)
      (𝓝 (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))) := by
  have := (fsLogReg_tendsto h u x hx hu).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have e : Real.log (‖∑ j, u j * x j‖ / h.dualNorm x) =
      Real.log ‖linEval u x‖ - Real.log (h.dualNorm x) :=
    Real.log_div (norm_pos_iff.2 hu).ne' hx.ne'
  rwa [fsLog, e] at this
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
