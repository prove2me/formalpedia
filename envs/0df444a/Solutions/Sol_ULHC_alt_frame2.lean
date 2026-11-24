-- Prove2me | solution 1 for ULHC.alt_frame2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:32.906324+00:00
-- url     : https://prove2.me/submissions/89063b92-6df6-4a27-a072-a8066b78c1ef

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_side_cases


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {w : Pt} {tw : Side} (s : Side)
    (bw : back w tw ∈ F) (fw : front w tw ∈ F) (l1 : lat1 w tw ∉ F) (l2 : lat2 w tw ∉ F) :
    (back w s ∈ F ↔ front w s ∈ F) ∧ (lat1 w s ∈ F ↔ lat2 w s ∈ F) ∧
      (back w s ∈ F ↔ lat1 w s ∉ F) := by
  rcases side_cases s tw with h | h | h | h <;> subst h
  · tauto
  · obtain ⟨f1, f2, fb, ff⟩ := frame_opp w s
    rw [f1] at l1; rw [f2] at l2; rw [fb] at bw; rw [ff] at fw
    tauto
  · obtain ⟨ff, fb, fl⟩ := frame_latA w s
    rw [ff] at fw; rw [fb] at bw
    rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at l1 <;> rw [h2] at l2 <;> tauto
  · obtain ⟨ff, fb, fl⟩ := frame_latB w s
    rw [ff] at fw; rw [fb] at bw
    rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at l1 <;> rw [h2] at l2 <;> tauto
end ULHC
