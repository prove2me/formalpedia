-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:37.853721+00:00
-- url     : https://prove2.me/submissions/c41b5112-42d6-4e7d-8afd-07dc4ee3b6e0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CommensuratedOfIsOpenIsCompact
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
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    Commensurated K := by
  intro x
  have hmo : IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    have hset : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
        (fun y => x⁻¹ * y * x) ⁻¹' (K : Set G) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact ho.preimage (by fun_prop)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have hso : IsOpen (((K.map (MulAut.conj x).toMonoidHom).subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite (K ⧸ (K.map (MulAut.conj x).toMonoidHom).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite
end PI.UnitaryGroupMassFormula.AdIndexEq
