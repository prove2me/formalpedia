-- Prove2me | solution 1 for ULHC.dval_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:20:58.203139+00:00
-- url     : https://prove2.me/submissions/a9e053d0-b963-4505-8f58-8c2ec4de6677

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_card_candN_le
import Theorems.Thm_ULHC_gw_le
import Theorems.Thm_ULHC_pw_le_len
import Theorems.Thm_ULHC_dval_eq
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_MP_isPath_cons
import Theorems.Thm_ULHC_MP_shortcut
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_crpath_to_path
import Theorems.Thm_ULHC_findPath_some
import Theorems.Thm_ULHC_path_to_crpath


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G : Finset Edge} (hGV : Inside V G) : dval V G ≤ Dm V := by
  rcases hp : findPath V G with _ | ⟨σ, L⟩
  · unfold dval
    rw [hp]
    exact Nat.zero_le _
  rw [dval_eq hp]
  obtain ⟨hP, hmin⟩ := findPath_some hGV hp
  obtain ⟨hpath, hN, _⟩ := crpath_to_path hGV hP
  generalize posList 1 (σ :: L) = q at hpath hN
  cases q with
  | nil => exact hpath.elim
  | cons x rest =>
    obtain ⟨hsrc, htail⟩ := MP.isPath_cons.1 hpath
    obtain ⟨L1, ht1, hnd, hsub⟩ := MP.shortcut htail
    have hpath1 : MP.IsPath (gsrc V G) gmid gtgt (gedge V G) (x :: L1) :=
      MP.isPath_cons.2 ⟨hsrc, ht1⟩
    have hN1 : ∀ z ∈ x :: L1, z ∈ candN V G := fun z hz => hN z (hsub.subset hz)
    obtain ⟨σ', L', _, hP', hw'⟩ := path_to_crpath hGV hpath1 hN1
    have hlen : (x :: L1).length ≤ (candN V G).card := by
      rw [← List.toFinset_card_of_nodup hnd]
      exact Finset.card_le_card (fun z hz => hN1 z (List.mem_toFinset.1 hz))
    have hpw := pw_le_len (fun z hz => gw_le (hN1 z hz))
    have hc := card_candN_le (V := V) G
    have hm := hmin σ' L' hP'
    have hmul : (x :: L1).length * V.card ≤ Bd V * V.card :=
      Nat.mul_le_mul_right _ (hlen.trans hc)
    unfold Dm
    omega
end ULHC
