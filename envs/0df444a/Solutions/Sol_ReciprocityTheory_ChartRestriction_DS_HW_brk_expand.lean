-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.brk_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:58:42.585044+00:00
-- url     : https://prove2.me/submissions/b2a8f752-aa3d-49d9-a173-b4744d4ce715

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
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] (a1 a2 b1 b2 : R) :
    (a1 + Complex.I • a2) * (b1 + Complex.I • b2) - (b1 + Complex.I • b2) * (a1 + Complex.I • a2) =
      (a1 * b1 - b1 * a1) + Complex.I • (a1 * b2 - b2 * a1) + Complex.I • (a2 * b1 - b1 * a2) +
        (Complex.I * Complex.I) • (a2 * b2 - b2 * a2) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, smul_sub]
  abel
end ReciprocityTheory.ChartRestriction.DS.HW
