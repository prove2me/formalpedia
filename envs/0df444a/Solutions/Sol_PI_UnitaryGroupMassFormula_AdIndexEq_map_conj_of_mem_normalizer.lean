-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.map_conj_of_mem_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:13.156501+00:00
-- url     : https://prove2.me/submissions/2f467d77-8ce0-4ef6-adb3-514bb39d3f60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
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
theorem _root_.solution (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj x).toMonoidHom = K := by
  have hx' : ∀ h, h ∈ K ↔ x * h * x⁻¹ ∈ K := by
    intro h
    have h2 := Subgroup.mem_normalizer_iff.mp hx h
    simpa using h2
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (hx' k).mp hk
  · intro hy
    refine ⟨x⁻¹ * y * x, (hx' _).mpr ?_, by group⟩
    convert hy using 1
    group
end PI.UnitaryGroupMassFormula.AdIndexEq
