-- Prove2me | solution 1 for ULHC.Ends.adj_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:40.07566+00:00
-- url     : https://prove2.me/submissions/df7c1ee6-15ee-459a-833b-537287bd928f

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_PStep_symm


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
namespace Ends
theorem _root_.solution {g : Edge} {s tf u v : Pt} (h : Ends g s tf)
    (huv : (g.p = u ∧ g.q = v) ∨ (g.p = v ∧ g.q = u)) :
    (u = s ∧ v = tf) ∨ (u = tf ∧ v = s) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases huv with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h3.symm.trans h1, h4.symm.trans h2⟩
  · exact Or.inr ⟨h4.symm.trans h2, h3.symm.trans h1⟩
  · exact Or.inr ⟨h3.symm.trans h1, h4.symm.trans h2⟩
  · exact Or.inl ⟨h4.symm.trans h2, h3.symm.trans h1⟩
end Ends
end ULHC
