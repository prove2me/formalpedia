-- Prove2me | solution 1 for ULHC.flip_step1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:47.938825+00:00
-- url     : https://prove2.me/submissions/45d614df-060b-4f3e-881b-7eb426e13c84

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_conn_erase_of_even
import Theorems.Thm_ULHC_conn_insert_of_conn
import Theorems.Thm_ULHC_ncomp_congr


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {x y : ℤ}
  (hV : Inside V F) (hc : IsCell V (x, y))
  (hb : bot (x, y) ∈ F) (ht : top (x, y) ∈ F) (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F)
  (h2 : ∀ z, (Conn F (x, y) z ∨ Conn F (x, y + 1) z) → deg F z = 2)
include hV hc hb ht hl hr h2
omit hc ht hl hr
namespace ULHC
theorem _root_.solution :
    Conn (F.erase (bot (x, y))) (x, y) (x + 1, y) ∧
      ncomp V (F.erase (bot (x, y))) = ncomp V F := by
  have hc1 : Conn (F.erase (bot (x, y))) (bot (x, y)).p (bot (x, y)).q := by
    apply conn_erase_of_even hV hb
    intro z _ hz
    rw [h2 z (Or.inl hz)]; exact even_two
  refine ⟨hc1, ?_⟩
  have := Finset.insert_erase hb
  conv_rhs => rw [← this]
  apply ncomp_congr
  intro u _ v _
  exact (conn_insert_of_conn hc1 u v).symm
end ULHC
