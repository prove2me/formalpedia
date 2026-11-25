-- Prove2me | solution 1 for PI.WGB.natW_anti_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:03.527421+00:00
-- url     : https://prove2.me/submissions/eafeb5eb-2760-4e88-a855-ea0428aadda9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)
end PI.WGB
