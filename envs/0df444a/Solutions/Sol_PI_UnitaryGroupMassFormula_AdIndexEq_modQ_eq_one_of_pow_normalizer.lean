-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_pow_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:14.622642+00:00
-- url     : https://prove2.me/submissions/73cf60de-deb1-4367-bf80-839f40e6d80a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_eq_one_of_mem_normalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_eq_one_of_pow

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
theorem _root_.solution (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ}
    (hm : m ≠ 0) (h : x ^ m ∈ Subgroup.normalizer (K : Set G)) : modQ K x = 1 := by
  exact modQ_eq_one_of_pow K hK x hm (modQ_eq_one_of_mem_normalizer K h)
end PI.UnitaryGroupMassFormula.AdIndexEq
