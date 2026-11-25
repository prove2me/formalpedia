-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_one_sub_eT_ne_zero_d011cad6a312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:40.417972+00:00
-- url     : https://prove2.me/submissions/58cacd7e-9a89-4e3d-8f61-0d8dec6522c2

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eT_coeff_364da66b02d3
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d
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
theorem _root_.solution [CharZero K] (g : Γ) (hg : g ≠ 1) : 1 - eT K Γ ≠ 0 := fun h => by
  have h1 := congrArg (fun x => x.coeff g) h
  simp only [coeff_sub, Finsupp.sub_apply, eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hg),
    zero_sub] at h1
  exact inv_ne_zero (card_ne (K := K) (Γ := Γ)) (neg_eq_zero.mp h1)
end Formalism.BasicNotions.Examples₂.NZ
