-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:18.776206+00:00
-- url     : https://prove2.me/submissions/71e8dc1e-8938-4b81-a582-adfbeb2523f9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lift_vector_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_coordinate_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution : Measurable (Ψt k r') := by
  unfold Ψt mk3
  have h1 : Measurable (fun p : ℂ × HPar k r' => hb k r' p.2.1 p.2.2) := heisenberg_coordinate_measurable.comp measurable_snd
  have h2 : Measurable (fun p : ℂ × HPar k r' => liftVec k 1 r' p.2.1) :=
    lift_vector_measurable.comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable (fun p : ℂ × HPar k r' => conj p.1) := Complex.continuous_conj.measurable.comp measurable_fst
  exact (((h1.div h3).smul_const _).add h2).add (measurable_fst.smul_const _)
end Formalism.FourierDecayAlt.P.B2x8
