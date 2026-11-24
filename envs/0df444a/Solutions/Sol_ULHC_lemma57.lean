-- Prove2me | solution 1 for ULHC.lemma57
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:21:44.68526+00:00
-- url     : https://prove2.me/submissions/8191a6a8-4a2f-4000-80fc-c04d482891eb

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Ends_isEdge
import Theorems.Thm_ULHC_cut_ends
import Theorems.Thm_ULHC_typeIII_classes
import Theorems.Thm_ULHC_end_inter
import Theorems.Thm_ULHC_alpha_typeIII
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_chain_border_l
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_on_chain_of_side
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
theorem _root_.solution (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {d : Pt}
    (hd : IsCell V d) (hd3 : ¬ NotTypeIII V (flipCol F c s (k + 2)) d) :
    ∃ d' ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)),
      ¬ NotTypeIII V (flipCol F c s (k + 2)) d' := by
  by_cases hγ : lat1 (cellJ c s (k + 2)) s ∈ F
  · by_contra hno
    have hC : ∀ d' ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)),
        NotTypeIII V (flipCol F c s (k + 2)) d' :=
      fun d' hd' => by_contra fun h => hno ⟨d', hd', h⟩
    have hF' : Deg2 V (flipCol F c s (k + 2)) :=
      deg2_flipCol _ F hF hpat (fun j hj => hcell j (by omega))
    obtain ⟨P, hB, hcut⟩ := chain_border_l hs hF' x0 hconn _ hC
    simp only [NotTypeIII, not_forall] at hd3
    obtain ⟨tf, hb, hf, hl1, hl2, hn⟩ := hd3
    obtain ⟨hI, hEB⟩ := end_inter hF hT hk hcell hpat hsep
    have hu := (hcut _ hI.1).2 hEB
    rw [cut_ends (ends_lat1 _ s)] at hu
    obtain ⟨b1, _, f1, _⟩ := isCell_corners hd tf
    have hE : IsEdge V (lat1 d tf) := (ends_lat1 d tf).isEdge b1 f1
    have hdc : Cut P (lat1 d tf) := by
      rw [cut_ends (ends_lat1 d tf)]
      rcases typeIII_classes hF hT hk hcell hpat hsep hγ hd hb hf hl1 hl2 hn with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hB.same_side h1, hB.same_side h2]; exact hu
      · rw [hB.same_side h1, hB.same_side h2]; tauto
    have hon := on_chain_of_side hd (by rw [cellE_frame d tf]; simp) ((hcut _ hE).1 hdc)
    exact hn (hC d hon tf hb hf hl1 hl2)
  · obtain ⟨hmem, h3⟩ := alpha_typeIII hF hT hk hcell hpat hsep hγ
    exact ⟨_, hmem, h3⟩
end ULHC
