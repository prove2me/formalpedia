-- Prove2me | solution 1 for PI.FJMX.monomialRightWeight_eq_weight_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:48.267957+00:00
-- url     : https://prove2.me/submissions/484e03a8-3eee-4edf-a760-0acd5cd7a67c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
import Theorems.Thm_PI_FJMX_weight_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (m : Ln p q r s →₀ ℕ) (y : Ix r s) :
    wt2 m y = (Finsupp.weight (rightPositiveIndicator y) m : ℤ) - (Finsupp.weight (rightNegativeIndicator y) m : ℤ) := by
  classical
  rw [weight_fin, weight_fin, wt2]
  push_cast
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single y]
  · cases h : linePos (a, y) <;> simp [rightPositiveIndicator, rightNegativeIndicator, h]
  · intro c _ hc
    simp [rightPositiveIndicator, rightNegativeIndicator, hc]
  · simp
end PI.FJMX
