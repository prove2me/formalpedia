-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B7_norm_pi__le_53d20754f3c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:11.478603+00:00
-- url     : https://prove2.me/submissions/15c2cedc-d35d-4583-abc5-c5478ec8c50f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {h : Mat k r} (hh : h ∈ UWset k r D.z') : ‖D.π' h‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [D.π'_unitary h hh v]
end Formalism.FourierDecayAlt.P.B7
