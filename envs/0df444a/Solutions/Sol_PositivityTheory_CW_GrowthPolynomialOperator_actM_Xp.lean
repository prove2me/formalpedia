-- Prove2me | solution 1 for PositivityTheory.CW.GrowthPolynomialOperator.actM_Xp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:24:59.590405+00:00
-- url     : https://prove2.me/submissions/097916ff-ac3f-40dd-8ae2-bd9f8af3d28c

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.GrowthPolynomialOperator
variable {n : ℕ}
namespace PositivityTheory.CW.GrowthPolynomialOperator
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Xp a b) = ((1 + Complex.I) / 2) • E a b + ((1 - Complex.I) / 2) • E b a := by
  simp only [actM, Xp, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.single_apply, ite_smul, zero_smul, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
end PositivityTheory.CW.GrowthPolynomialOperator
