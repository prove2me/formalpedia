-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inl_e5d50e568d36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:30.452427+00:00
-- url     : https://prove2.me/submissions/cba851c3-4fec-4a9b-a40f-7dcdd6a2c216

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
theorem _root_.solution (i : Fin e) : ∑ m, val e I j (.inl (i, m)) * cx e I j m = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inl (i, m.1)) = X (.inl (i, m)) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (-(∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)) * cinv_mul_cx e I j
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
