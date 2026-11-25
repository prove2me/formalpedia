-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_proof_c9a9d1e661b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:17.404414+00:00
-- url     : https://prove2.me/submissions/5d2e2516-0dde-42f1-b0de-dfaa5f275c92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrictQuotX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_quotH_equiv_a468c3a14426
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74


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
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace PrimeFiltration.RestrictQuot
theorem _root_.solution : PrimeFiltration.RestrictQuot.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX K' _ _ ψ hker hxy Q Q' r hRD c i
  have hpy : primeOf (S := S) (fun l => ψ (ratio hj l)) = pp :=
    (PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hj hX).2 K' ψ hker
  have hle' : primeOf (S := S) x ≤ primeOf (S := S) (fun l => ψ (ratio hj l)) := hpy ▸ hle
  obtain ⟨rc, hrc⟩ := RestrictTwist.restrictData_twist (Q₂ := twistBundle S x c)
    (Q₂' := twistBundle S (fun l => ψ (ratio hj l)) c) hRD
    (RestrictTwist.restrictData_twistSys hxy hle' c)
  exact PrimeFiltration.RestrictQuot.quotH_equiv (L := Q.tensor (twistBundle S x c))
    (L' := Q'.tensor (twistBundle S (fun l => ψ (ratio hj l)) c)) hrc hpy i
end PrimeFiltration.RestrictQuot
end GroundTheory.Heights₂.Heights.Kleiman
