-- Prove2me | solution 1 for ULHC.cr2B_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:44.10849+00:00
-- url     : https://prove2.me/submissions/8023ee19-f27d-454d-b4c4-9b992505dc36

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_mem_allStrips
import Theorems.Thm_ULHC_connB_iff
import Theorems.Thm_ULHC_corners_mem
import Theorems.Thm_ULHC_sideOffB_iff
import Theorems.Thm_ULHC_midB_iff
import Theorems.Thm_ULHC_bool_not_iff
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) {b c : StripSpec} (hu : IsCell V (endCell b)) :
    cr2B V G b c = true ↔ CR2 V G b c := by
  have hFu : Inside V (flip G (endCell b)) := inside_flip hGV hu
  unfold cr2B CR2
  simp only [Bool.and_eq_true, decide_eq_true_eq, mem_allStrips, sideOffB_iff,
    bool_not_iff midB_iff]
  have hne : notEndB b c = true ↔ ∀ j < c.n, cellJ c.c c.s j ≠ endCell b := by
    simp [notEndB, List.all_eq_true, List.mem_range]
  have hend : endOffB b c = true ↔
      (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b)) := by
    simp only [endOffB, decide_eq_true_eq]
  rw [hne, hend]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, he⟩, h1, hp, hc⟩, hso⟩, hne'⟩, hen⟩, hm1⟩, hm2⟩, hcg⟩, hcu⟩
    have hc0 : IsCell V c.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 c.s
    refine ⟨h2, he, h1, hp, hc, hso, hne', hen, hm1, hm2, (connB_iff hGV hb hf).1 hcg, ?_⟩
    exact (bool_not_iff (connB_iff hFu hb hf)).1 hcu
  · rintro ⟨h2, he, h1, hp, hc, hso, hne', hen, hm1, hm2, hcg, hcu⟩
    have hc0 : IsCell V c.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 c.s
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, he⟩, h1, hp, hc⟩, hso⟩, hne'⟩, hen⟩, hm1⟩, hm2⟩,
      (connB_iff hGV hb hf).2 hcg⟩, (bool_not_iff (connB_iff hFu hb hf)).2 hcu⟩
end ULHC
