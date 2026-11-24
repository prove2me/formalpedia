-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp__f6287b255e07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:00:07.656691+00:00
-- url     : https://prove2.me/submissions/e59111e3-633c-4919-9a04-f53c4307ae96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (a b : Fin n) :
    Matrix.single b a (1 : ℂ) = -kp1 a b + Complex.I • kp2 a b := by
  unfold kp1 kp2
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul]
  have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [← mul_assoc, hI]
  split_ifs <;> ring
end ReciprocityTheory.ChartRestriction.DS.HW
