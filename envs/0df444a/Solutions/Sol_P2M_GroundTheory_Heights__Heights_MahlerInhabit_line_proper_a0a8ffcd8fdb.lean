-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:36.468453+00:00
-- url     : https://prove2.me/submissions/ffac1f03-5b52-4f4f-acb8-8d662a994f18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
open GroundTheory.Heights₂.Heights.MahlerInhabit
namespace GroundTheory.Heights₂.Heights.MahlerInhabit
theorem _root_.solution (a b : Fin 2) (hab : a ≠ b) :
    IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (coord a)) (coord b) := by
  intro W' hW' hXb
  rw [linForm_coord] at hXb
  have hmem : W' ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ⊔ Ideal.span {linForm (coord a)}) := by
    by_contra hc
    apply Finsupp.mem_support_iff.mp hW'
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    exact if_neg hc
  obtain ⟨hmin, j, hj⟩ := hmem
  have hXa : X a ∈ W' := by
    apply hmin.1.2
    rw [← linForm_coord]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  have : j = a ∨ j = b := by fin_cases a <;> fin_cases b <;> fin_cases j <;> simp_all
  rcases this with rfl | rfl
  · exact hj hXa
  · exact hj hXb
end GroundTheory.Heights₂.Heights.MahlerInhabit
