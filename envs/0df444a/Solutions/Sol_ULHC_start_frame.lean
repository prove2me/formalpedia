-- Prove2me | solution 1 for ULHC.start_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:36:10.084534+00:00
-- url     : https://prove2.me/submissions/453e36e3-6868-47ea-aae5-e24df9bdbd73

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_side_cases


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {d : Pt} {tf : Side} (s : Side) (hb : back d tf ∈ F)
    (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F)) :
    ((tf = s ∨ tf = s.opp) ∧ (lat1 d s ∈ F ↔ lat2 d s ∉ F)) ∨
      ((tf = latA s ∨ tf = latB s) ∧ (lat1 d s ∈ F ∨ lat2 d s ∈ F) ∧
        (back d s ∈ F ↔ front d s ∉ F)) := by
  rcases side_cases s tf with h | h | h | h <;> subst h
  · left; refine ⟨Or.inl rfl, ?_⟩; tauto
  · left; refine ⟨Or.inr rfl, ?_⟩
    rw [(frame_opp d s).1, (frame_opp d s).2.1] at hxl; tauto
  · right; refine ⟨Or.inl rfl, ?_, ?_⟩
    · rw [(frame_latA d s).2.1] at hb; exact Or.inr hb
    · rcases (frame_latA d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hxl <;> tauto
  · right; refine ⟨Or.inr rfl, ?_, ?_⟩
    · rw [(frame_latB d s).2.1] at hb; exact Or.inl hb
    · rcases (frame_latB d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hxl <;> tauto
end ULHC
