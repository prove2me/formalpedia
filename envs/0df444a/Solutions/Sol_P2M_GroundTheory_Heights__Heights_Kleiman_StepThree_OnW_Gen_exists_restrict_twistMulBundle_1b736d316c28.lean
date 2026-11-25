-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_twistMulBundle_1b736d316c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:55.78736+00:00
-- url     : https://prove2.me/submissions/b5b99482-20a4-4266-be91-19e960d94581

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubvarDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_exists_restrict_powBundle_537c07f8abf7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Extension_proof_3fa22c8847fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Generated_proof_7390091ed2be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Restrict_proof_9254d696b6ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_JProper_proof_0fc41ca14e1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubvarDrop_proof_4b488f96c14b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistAlg_proof_fef5e6275e9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleNefPlusAmple_proof_cc5777b7bc68


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
theorem _root_.solution (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (p : ℕ) (m : ℤ) :
    ∃ r' : Ω → K', RestrictData (twistMulBundle M p m).toSubSystem hxy
      (twistMulBundle M' p m).toSubSystem r' := by
  obtain ⟨rP, hrP⟩ := exists_restrict_powBundle hxy hle M M' r h p
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 S Ω N x K' y hxy hle m
  exact RestrictTwist.proof.2 S Ω N x K' y hxy _ (twistBundle S x m) _ (twistBundle S y m) rP rc hrP hrc
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
