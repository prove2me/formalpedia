-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:38.606267+00:00
-- url     : https://prove2.me/submissions/c3e986f5-9a99-4163-84f2-724183d84a90

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution : Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => act p.2 p.1) := by
  refine measurable_pi_iff.2 fun i => ?_
  show Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => ∑ j, invM p.2 i j * p.1 j)
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (invM_meas.comp measurable_snd))).mul
    ((measurable_pi_apply j).comp measurable_fst)
end Formalism.FourierDecayAlt.P.TwoByOneBlock
