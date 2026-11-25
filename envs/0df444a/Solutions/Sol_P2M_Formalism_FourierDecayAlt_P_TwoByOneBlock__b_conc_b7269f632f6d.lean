-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_conc_b7269f632f6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:53.56873+00:00
-- url     : https://prove2.me/submissions/d0a0da74-3a38-4bc4-abac-aaef2935c9fd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Nq_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Nq_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_scl_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_shell_meas

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
theorem _root_.solution {T' : ℝ} (hT' : 0 < T') : ∀ᵐ u ∂σb k T', Nq k u = T' := by
  unfold σb
  rw [ae_map_iff (scl_meas T').aemeasurable (measurableSet_eq_fun Nq_cont.measurable measurable_const),
    ae_restrict_iff' (shell_meas T')]
  refine Filter.Eventually.of_forall fun u hu => ?_
  unfold scl
  rw [Nq_smul, Real.sq_sqrt (div_nonneg hT'.le hu.1.le), div_mul_cancel₀ _ hu.1.ne']
end Formalism.FourierDecayAlt.P.TwoByOneBlock
