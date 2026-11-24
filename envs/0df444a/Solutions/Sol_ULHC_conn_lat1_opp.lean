-- Prove2me | solution 1 for ULHC.conn_lat1_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:27.459372+00:00
-- url     : https://prove2.me/submissions/536d6e80-2cf3-4e7e-81fa-990fec071d55

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_ends_unique
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_frame_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {A : Finset Edge} {d : Pt} {s : Side}
    (h : ¬ Conn A (back1 d s) (front1 d s)) : ¬ Conn A (back1 d s.opp) (front1 d s.opp) := by
  have e1 := ends_lat1 d s.opp
  rw [(frame_opp d s).1] at e1
  rcases ends_unique (ends_lat1 d s) e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact h
  · rw [← h1, ← h2]; exact fun h' => h h'.symm
end ULHC
