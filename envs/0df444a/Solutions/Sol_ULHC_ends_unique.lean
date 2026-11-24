-- Prove2me | solution 1 for ULHC.ends_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:16.090681+00:00
-- url     : https://prove2.me/submissions/f937436a-a56b-4ad5-9ffd-4d25438951a8

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_PStep_symm


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {e : Edge} {u v u' v' : Pt} (h : Ends e u v) (h' : Ends e u' v') :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  · exact Or.inr ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  · exact Or.inr ⟨h2.symm.trans h4, h1.symm.trans h3⟩
  · exact Or.inl ⟨h2.symm.trans h4, h1.symm.trans h3⟩
end ULHC
