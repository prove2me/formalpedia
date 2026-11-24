-- Prove2me | solution 1 for ULHC.validB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:20.652564+00:00
-- url     : https://prove2.me/submissions/16ea2243-41de-4e14-9a3e-0b3d3b36ff1e

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_mem_allStrips
import Theorems.Thm_ULHC_connB_iff
import Theorems.Thm_ULHC_corners_mem
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F G : Finset Edge}
namespace ULHC
theorem _root_.solution (hFV : Inside V F) {σ : StripSpec} :
    validB V F σ = true ↔ ValidStrip V F σ := by
  unfold validB ValidStrip
  rw [Bool.and_eq_true, decide_eq_true_eq, mem_allStrips, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h1, hp, hc⟩, hn⟩
    have hc0 : IsCell V σ.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 σ.s
    refine ⟨h1, hp, hc, fun h => ?_⟩
    rw [← connB_iff hFV hb hf] at h
    rw [h] at hn; cases hn
  · rintro ⟨h1, hp, hc, hn⟩
    have hc0 : IsCell V σ.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 σ.s
    refine ⟨⟨h1, hp, hc⟩, ?_⟩
    cases h : connB V F (back1 σ.c σ.s) (front1 σ.c σ.s)
    · rfl
    · exact absurd ((connB_iff hFV hb hf).1 h) hn
end ULHC
