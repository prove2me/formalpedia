-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_hypotheses_inhabited_dc2ae0cc071b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:18.530131+00:00
-- url     : https://prove2.me/submissions/ed5652c6-2ec9-47de-9ad0-4d9564a27592

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_incidenceIdeal_pointZeroOne_le_span_43596e420577
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_uLine_fb22ac47c882
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_uLine_not_mem_bot_330a39a70e2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_prime_qLine_c53c4192a86d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quot_bot_acd27392687d


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
namespace GroundTheory.Heights₂.Heights
namespace ComponentOfIncIdeal
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) =
        ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsProjPrime (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ∧
      (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine} ≤
        Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∧
      Prime qLine ∧
      incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ≤ Ideal.span {qLine} :=
  ⟨LineChowForm.isProjPrime_line, ringKrullDim_quot_bot ℚ 2, linForm_uLine_not_mem_bot,
    isProjPrime_span_X_zero ℚ, by rw [bot_sup_eq, linForm_uLine], prime_qLine, incidenceIdeal_pointZeroOne_le_span⟩
end ComponentOfIncIdeal
end GroundTheory.Heights₂.Heights
