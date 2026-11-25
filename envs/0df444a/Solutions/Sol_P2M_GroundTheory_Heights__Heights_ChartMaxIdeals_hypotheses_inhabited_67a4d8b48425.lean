-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_hypotheses_inhabited_67a4d8b48425
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:29.757752+00:00
-- url     : https://prove2.me/submissions/08d89869-8ddd-43f3-92c8-ae8cf361cc02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c

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
namespace ChartMaxIdeals
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine :=
  line_section
end ChartMaxIdeals
end GroundTheory.Heights₂.Heights
