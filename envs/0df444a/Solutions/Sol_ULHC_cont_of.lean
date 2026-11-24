-- Prove2me | solution 1 for ULHC.cont_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:33:17.751632+00:00
-- url     : https://prove2.me/submissions/402b3695-84cd-43ee-8cc3-29fc4f7589e8

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_PStep_symm


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {P : Prop} {i m : ℕ} (gf : P ↔ (i % 2 = 1 ↔ i + 1 < m)) (h : P ↔ i % 2 = 1) :
    i + 1 < m := by
  have e2 := gf.symm.trans h
  by_contra hm
  rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
  · exact absurd (e2.1 ⟨fun h' => by omega, fun h' => absurd h' hm⟩) (by omega)
  · exact hm ((e2.2 h0).1 h0)
end ULHC
