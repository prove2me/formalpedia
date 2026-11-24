-- Prove2me | solution 1 for ULHC.typeIII_classes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:25.429075+00:00
-- url     : https://prove2.me/submissions/4281f955-0efa-4ef3-957f-48ff2510069c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_darkened_cell_notTypeIII
import Theorems.Thm_ULHC_mid_not_end
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_end_not_mid
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_strip_even_rel
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution (hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} (hd : IsCell V d)
    {tf : Side} (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf)) :
    (Conn (flipCol F c s (k + 2)) (back1 d tf) (back1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) (front1 d tf) (front1 (cellJ c s (k + 1)) s)) ∨
      (Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) (front1 d tf) (back1 (cellJ c s (k + 1)) s)) := by
  set F' := flipCol F c s (k + 2)
  have hT' : ¬ NotTypeIII V F' d := fun h => hn (h tf hb hf hl1 hl2)
  have hbd : back d tf ∈ cellE d := by rw [cellE_frame d tf]; simp
  have hfd : front d tf ∈ cellE d := by rw [cellE_frame d tf]; simp
  -- The two dark sides were dark before the flip.
  have hbF : back d tf ∈ F := by
    by_contra h; exact hT' (darkened_cell_notTypeIII hF hT hk hcell hpat hsep hγ hb h hbd)
  have hfF : front d tf ∈ F := by
    by_contra h; exact hT' (darkened_cell_notTypeIII hF hT hk hcell hpat hsep hγ hf h hfd)
  -- Their ends were joined before the flip.
  have hxy : Conn F (back1 d tf) (front1 d tf) := by
    by_cases h1 : lat1 d tf ∈ F
    · exact (ends_lat1 d tf).conn h1
    by_cases h2 : lat2 d tf ∈ F
    · exact (((ends_back d tf).conn hbF).trans ((ends_lat2 d tf).conn h2)).trans
        ((ends_front d tf).conn hfF).symm
    · exact hT d hd tf hbF hfF h1 h2
  -- The ends are not middle corners.
  have nx : ¬ IsMid c s k (back1 d tf) := fun hz =>
    hT' (mid_not_end hF hk hcell hpat hγ hz hb (((ends_back d tf).inc_iff _).2 (Or.inl rfl))
      hbd)
  have ny : ¬ IsMid c s k (front1 d tf) := fun hz =>
    hT' (mid_not_end hF hk hcell hpat hγ hz hf (((ends_front d tf).inc_iff _).2 (Or.inl rfl))
      hfd)
  -- Transfer through the split and the odd part.
  obtain ⟨F1, _, _, _, hrel, hfine, hodd⟩ :=
    strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  obtain ⟨na, nb'⟩ := end_not_mid c s k
  have up : ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y → Conn F1 x y → Conn F' x y :=
    fun x y hx hy h => (hodd x y hx hy).2 (Or.inl h)
  have h1 : ¬ Conn F1 (back1 d tf) (front1 d tf) := fun h => hn (up _ _ nx ny h)
  rcases (hfine _ _).1 hxy with h | ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact absurd h h1
  · exact Or.inl ⟨up _ _ nx na h2, (up _ _ nb' ny h3).symm⟩
  · exact Or.inr ⟨up _ _ nx nb' h2, (up _ _ na ny h3).symm⟩
end ULHC
