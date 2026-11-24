-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:59:01.610965+00:00
-- url     : https://prove2.me/submissions/086c3059-6fbd-43e3-be9f-bdb5bc319d5c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_natCast_succ_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f' : Mat k r → E} {U : Set (Mat k r)} (m : ℕ) (b : Bool) (X : Mat k r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U) :
    ContDiffOn ℝ (((m : ℕ) : ℕ∞) : WithTop ℕ∞) (op' b X f') U := by
  exact (hf.fderiv_of_isOpen hU (natCast_succ_le m)).clm_apply (vf b X).contDiff.contDiffOn
end Formalism.FourierDecayAlt.P.B4
