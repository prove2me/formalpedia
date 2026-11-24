-- Prove2me | solution 1 for ULHC.start_notTypeIII
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:47:23.735022+00:00
-- url     : https://prove2.me/submissions/a4adc4a2-1643-45b2-b182-9589ad95b24c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_allConn_of_frame
import Theorems.Thm_ULHC_notTypeIII_of_allConn
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_not_mem
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_not_mid_back2
import Theorems.Thm_ULHC_not_mid_start
import Theorems.Thm_ULHC_strip_even_rel


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution : NotTypeIII V (flipCol F c s (k + 2)) c := by
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ :=
    strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  have hl1 := (lat1_after hk hpat (j := 0) (by omega)).2 rfl
  have hl2 := (lat2_after hk hpat (j := 0) (by omega)).2 rfl
  rw [cellJ_zero] at hl1 hl2
  have c1 : Conn (flipCol F c s (k + 2)) (back1 c s) (front1 c s) := (ends_lat1 c s).conn hl1
  have c2 : Conn (flipCol F c s (k + 2)) (back2 c s) (front2 c s) := (ends_lat2 c s).conn hl2
  have hbF1 : back c s ∈ F1 := by
    rw [hF1, mem_flip_iff]
    have := back_not_mem c s (m := k + 1) (by omega)
    have := hpat.1
    tauto
  have c3 : Conn F1 (back1 c s) (back2 c s) := (ends_back c s).conn hbF1
  have c3' : Conn (flipCol F c s (k + 2)) (back1 c s) (back2 c s) :=
    (hodd _ _ (not_mid_start c s k).1 (not_mid_back2 c s k)).2 (Or.inl c3)
  exact notTypeIII_of_allConn (allConn_of_frame s c3' c1 (c3'.trans c2))
end ULHC
