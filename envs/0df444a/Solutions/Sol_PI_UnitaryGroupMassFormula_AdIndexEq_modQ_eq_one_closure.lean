-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:24.928913+00:00
-- url     : https://prove2.me/submissions/b64de64a-c22f-483f-9747-415dfef88e3f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
variable {G : Type} [Group G]
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (S : Set G)
    (hS : ∀ s ∈ S, modQ K s = 1) : ∀ x ∈ Subgroup.closure S, modQ K x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact modQ_one K
  | mul a b _ _ ha hb => rw [modQ_mul K hK, ha, hb, one_mul]
  | inv a _ ha => rw [modQ_inv, ha, inv_one]
end PI.UnitaryGroupMassFormula.AdIndexEq
