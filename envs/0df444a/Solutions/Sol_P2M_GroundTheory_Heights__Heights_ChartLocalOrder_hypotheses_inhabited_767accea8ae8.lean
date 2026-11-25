-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLocalOrder_hypotheses_inhabited_767accea8ae8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:03.653386+00:00
-- url     : https://prove2.me/submissions/3e8ca477-dfa2-4728-83d0-cd17156b1e1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_line_component_84026460324b

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
namespace ChartLocalOrder
theorem _root_.solution :
    (IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine) ∧
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) :=
  ⟨line_section, line_component⟩
end ChartLocalOrder
end GroundTheory.Heights₂.Heights
