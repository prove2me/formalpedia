-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x9_ae_ne__c879158f29b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:36.13979+00:00
-- url     : https://prove2.me/submissions/6ba67dd0-1b39-4a64-a32b-73ec9fdf4f2c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_xi_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_xi_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_cone_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_ae_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulVec_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cone_eq


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (CI : ConeInv) (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) :
    ∀ᵐ p : ℂ × HPar k r' ∂(mCone k r'), (a *ᵥ xi k r' p) (iL k r') ≠ 0 := by
  have hx : Measurable (xi k r') := xi_cont.measurable
  have ha' : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => a *ᵥ v := (mulVec_cont a).measurable
  have hS : MeasurableSet {v : Fin (2 * (1 + r') + k + 1) → ℂ | v (iL k r') ≠ 0} := by
    first
      | exact (measurableSet_eq_fun (measurable_pi_apply _) measurable_const).compl
      | measurability
  have h1 : ∀ᵐ v ∂(coneMeas k r'), v (iL k r') ≠ 0 := by
    rw [cone_eq, ae_map_iff hx.aemeasurable hS]
    filter_upwards [ae_ne (k := k) (r' := r')] with p hp
    rwa [xi_last]
  have h2 : ∀ᵐ v ∂(coneMeas k r'), (a *ᵥ v) (iL k r') ≠ 0 := by
    rw [← CI k r' a ha] at h1
    exact (ae_map_iff ha'.aemeasurable hS).1 h1
  rw [cone_eq] at h2
  exact (ae_map_iff hx.aemeasurable (ha' hS)).1 h2
end Formalism.FourierDecayAlt.P.B2x9
