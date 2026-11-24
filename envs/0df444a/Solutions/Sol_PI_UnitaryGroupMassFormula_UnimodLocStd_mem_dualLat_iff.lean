-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.mem_dualLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:20.422207+00:00
-- url     : https://prove2.me/submissions/4efe3f70-2490-42de-979f-31e8d210de81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (H : Sesq V) (Λ : AddSubgroup V) (x : V) :
    x ∈ dualLat H Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, altE H x y = k := by
  exact Iff.rfl
end PI.UnitaryGroupMassFormula.UnimodLocStd
