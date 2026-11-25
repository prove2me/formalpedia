-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_proof_e4472f073e25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:17.496051+00:00
-- url     : https://prove2.me/submissions/5c78a3bb-eb2a-4fd2-8a14-fd8b7dc11034

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_mem_incIdeal_of_aeval_eq_zero_a50fea87279f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_eq_zero_of_mem_incIdeal_ca256b480e30

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceGeneric
namespace GroundTheory.Heights₂.Heights.IncidenceGeneric
theorem _root_.solution (h₁ : FGNullstellensatz.Statement) : IncidenceGeneric.Statement := by
  intro F _ n k P _ c hc g
  exact ⟨aeval_eq_zero_of_mem_incIdeal h₁ P c hc g, mem_incIdeal_of_aeval_eq_zero P c g⟩
end GroundTheory.Heights₂.Heights.IncidenceGeneric
