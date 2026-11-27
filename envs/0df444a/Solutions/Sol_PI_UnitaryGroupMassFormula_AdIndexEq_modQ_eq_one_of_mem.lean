-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_eq_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:29:56.251484+00:00
-- url     : https://prove2.me/submissions/c939724b-1c8c-4ac6-9fa3-07ccac4d489e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_eq_one_of_mem_normalizer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
variable {G : Type} [Group G]
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (K : Subgroup G) {k : G} (hk : k ∈ K) : modQ K k = 1 := by
  apply modQ_eq_one_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro h
  try simp only [SetLike.mem_coe]
  constructor
  · intro hh
    exact K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)
  · intro hh
    have h2 := K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk
    simpa [mul_assoc] using h2
end PI.UnitaryGroupMassFormula.AdIndexEq
