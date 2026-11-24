-- Prove2me | solution 1 for ULHC.perp_bf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:40:42.351458+00:00
-- url     : https://prove2.me/submissions/a8e3473f-1251-42a0-ac97-2787cee60c64

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {d : Pt} {s tf : Side} {P : Prop} (g1 : lat1 d tf ∈ F ↔ P)
    (g2 : lat2 d tf ∈ F ↔ P)
    (fl : (lat1 d tf = back d s ∧ lat2 d tf = front d s) ∨ (lat1 d tf = front d s ∧ lat2 d tf = back d s)) :
    back d s ∈ F ↔ front d s ∈ F := by
  rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at g1; rw [h2] at g2; exact g1.trans g2.symm
  · rw [h1] at g1; rw [h2] at g2; exact g2.trans g1.symm
end ULHC
