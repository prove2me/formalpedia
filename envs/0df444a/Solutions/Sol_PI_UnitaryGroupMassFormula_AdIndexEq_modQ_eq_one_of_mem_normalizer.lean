-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_mem_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:28.794979+00:00
-- url     : https://prove2.me/submissions/a2d7939b-de4a-48a7-8d45-5782827031fc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_eq_one_of_map_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_map_conj_of_mem_normalizer

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
theorem _root_.solution (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    modQ K x = 1 := by
  exact modQ_eq_one_of_map_eq K x (map_conj_of_mem_normalizer K hx)
end PI.UnitaryGroupMassFormula.AdIndexEq
