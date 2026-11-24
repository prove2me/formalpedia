-- Prove2me | solution 1 for ULHC.ulhc_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:48:32.291541+00:00
-- url     : https://prove2.me/submissions/01e8db86-22bf-4fbb-83ad-598385523d01

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_extra_le
import Theorems.Thm_ULHC_run_complete
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_conn_of_ncomp_one
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_twoFactor_none
import Theorems.Thm_ULHC_twoFactor_some


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} (hs : Solid V) {H : Finset Edge} (hH : Deg2 V H)
    (hHam : ncomp V H = 1) (hPC : PathComplete V) : ulhc V = true := by
  have hne : V.Nonempty := by
    have hc : 0 < (V.image (cls V H)).card := by
      unfold ncomp at hHam
      omega
    exact Finset.image_nonempty.1 (Finset.card_pos.1 hc)
  obtain ⟨x0, hx0⟩ := hne
  have hconn : ∀ z ∈ V, Conn (GE V) x0 z := fun z hz =>
    (conn_of_ncomp_one hHam hx0 hz).mono (fun e he => mem_GE.2 (hH.1 e he))
  unfold ulhc
  rcases hf : twoFactor V with _ | F
  · exact absurd ⟨H, hH⟩ (twoFactor_none hf)
  have hF := twoFactor_some hf
  apply run_complete hs x0 hconn hPC ⟨x0, hx0⟩ _ F hF
  have h1 := extra_le hF.1
  have h2 : ncomp V F ≤ V.card := Finset.card_image_le
  have h3 : ncomp V F * (2 * Dm V + 4) ≤ V.card * (2 * Dm V + 4) := Nat.mul_le_mul_right _ h2
  unfold fuel
  rw [Nat.succ_mul]
  omega
end ULHC
