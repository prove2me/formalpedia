-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.ex_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:36.537663+00:00
-- url     : https://prove2.me/submissions/1b71a131-f317-4d15-88e7-1a8f9ffca140

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_FglPhSplit_Wk_compositionalInverseSymm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}
namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW
theorem _root_.solution (hd : Data l ex ph) : PowerSeries.subst l ex = PowerSeries.X :=
  (PI.FglPhSplit.Wk.compositionalInverseSymm ℂ_[p] l ex hd.1 hd.2.1).2
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
