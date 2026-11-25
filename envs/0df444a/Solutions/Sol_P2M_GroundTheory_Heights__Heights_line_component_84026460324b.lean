-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_line_component_84026460324b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:59.934796+00:00
-- url     : https://prove2.me/submissions/5fa8f2d1-127c-47f4-a535-821aaf9725dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_qLine_mem_incIdeal_b37e658e70cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944


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
open LineChowForm
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} :=
  ⟨span_X_zero_mem_relComps ℚ, qLine_mem_incIdeal, linearFormLine_not_mem_span_X0⟩
end GroundTheory.Heights₂.Heights
