-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GreenSymmetry_hypotheses_inhabited_2fbf7471ddd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:24.253519+00:00
-- url     : https://prove2.me/submissions/49abf877-c38d-4f93-a4ac-cded4b10f851

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_linForm_line_66a12de41669


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
open MvPolynomial MeasureTheory
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace GreenSymmetry
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∃ g : MvPolynomial (Fin (0 + 2) × Fin 2) ℂ, IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (0 + 2) g) ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∀ W' ∈ (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0)).support,
        linForm (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) ∉ W') := by
  have h0 : linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) = X 0 := by
    simp [linForm]
  have h1 : linForm (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) = X 1 := by
    simp [linForm]
  refine ⟨LineChowForm.isProjPrime_line, ⟨LineChowForm.D2, LineChowForm.isChowForm_line⟩,
    LineChowForm.linForm_line, ?_, ?_⟩
  · rw [h1, Ideal.mem_bot]; exact X_ne_zero _
  · intro W' hW' hX1
    rw [h1] at hX1
    have hmem : W' ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ⊔
        Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0)}) := by
      by_contra hc
      apply Finsupp.mem_support_iff.mp hW'
      simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
      exact if_neg hc
    obtain ⟨hmin, j, hj⟩ := hmem
    have hX0 : X 0 ∈ W' := by
      apply hmin.1.2
      rw [h0]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    fin_cases j
    · exact hj hX0
    · exact hj hX1
end GreenSymmetry
end GroundTheory.Heights₂.Heights
