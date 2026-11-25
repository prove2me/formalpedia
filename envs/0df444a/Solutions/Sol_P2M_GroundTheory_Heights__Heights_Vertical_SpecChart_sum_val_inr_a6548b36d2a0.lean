-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inr_a6548b36d2a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:08.942654+00:00
-- url     : https://prove2.me/submissions/d981db64-e702-4a28-85b5-e0db9377a52a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_cinv_mul_cx_d1cdfb4307c6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution : ∑ m, val e I j (.inr m) * cx e I j m - 1 = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inr m.1) = X (.inr m) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m) * cinv_mul_cx e I j
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
