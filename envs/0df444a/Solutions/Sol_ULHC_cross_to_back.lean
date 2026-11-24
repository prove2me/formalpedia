-- Prove2me | solution 1 for ULHC.cross_to_back
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:28.491626+00:00
-- url     : https://prove2.me/submissions/4e4ebe49-cbe8-45d1-8e23-ac312948f609

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_perp_pair
import Theorems.Thm_ULHC_front_to_back
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {A : Finset Edge} {d : Pt} {s tf : Side} (ht : tf = latA s ∨ tf = latB s)
    (h1 : lat1 d s ∈ A) (h2 : lat2 d s ∈ A) (hn : ¬ Conn A (back1 d tf) (front1 d tf)) :
    ¬ Conn A (back1 d s) (back2 d s) := by
  rcases perp_pair d ht with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hn
  · exact hn
  · exact fun h => hn h.symm
  · exact front_to_back h1 h2 hn
  · exact front_to_back h1 h2 (fun h => hn h.symm)
end ULHC
