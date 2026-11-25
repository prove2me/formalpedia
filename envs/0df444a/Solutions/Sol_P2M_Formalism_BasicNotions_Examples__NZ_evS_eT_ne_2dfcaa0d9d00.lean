-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_evS_eT_ne_2dfcaa0d9d00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:58.80421+00:00
-- url     : https://prove2.me/submissions/50a58375-e4bd-48ef-9c36-8dd4d12bdb62

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_eq_5f3a4c43d764
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) : evS ψ (eT K Γ) = 0 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq]
  simp only [eT_coeff, ← Finset.mul_sum]
  have h1 : ψ g * ∑ x, ψ x = ∑ x, ψ x := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g) (fun x => ψ x)]
    exact Finset.sum_congr rfl fun x _ => (map_mul ψ g x).symm
  have h2 : (ψ g - 1) * ∑ x, ψ x = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rw [(mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hg), mul_zero]
end Formalism.BasicNotions.Examples₂.NZ
