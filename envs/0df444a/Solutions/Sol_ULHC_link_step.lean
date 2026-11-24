-- Prove2me | solution 1 for ULHC.link_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:59:08.198835+00:00
-- url     : https://prove2.me/submissions/815408d2-c411-4fc7-87ea-0ea2664e576c

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
import Theorems.Thm_ULHC_flipCol_off
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_created_step
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_stripPat_congr
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
    {b c : StripSpec} (hb : ValidStrip V G b) (hl : CR2 V G b c) : ValidStrip V (applyS G b) c := by
  obtain ⟨h2, hev, hc1, hpatc, hcellc, hoff, hne, _, hm1, hm2, hxy, hsplit⟩ := hl
  obtain ⟨_, hpatb, hcellb, hsepb⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k, b.n = k + 2 := ⟨b.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  have hend : endCell b = cellJ b.c b.s (k + 1) := by unfold endCell; rw [hk]; rfl
  rw [hk] at hpatb hcellb hm1 hm2
  rw [hend] at hpatc hsplit
  have hcellb' : ∀ j ≤ k + 1, IsCell V (cellJ b.c b.s j) := fun j hj => hcellb j (by omega)
  have hsame := end_same hT hk2 hcellb' hpatb
  have hm1' : ¬ IsMid b.c b.s k (back1 c.c c.s) := by simpa using hm1
  have hm2' : ¬ IsMid b.c b.s k (front1 c.c c.s) := by simpa using hm2
  unfold applyS
  rw [hk]
  refine ⟨hc1, ?_, hcellc, created_step hk2 hG hcellb' hpatb hsepb hsame hxy hsplit hm1' hm2'⟩
  obtain ⟨n, hn⟩ : ∃ n, c.n = n + 1 := ⟨c.n - 1, by omega⟩
  rw [hn] at hpatc ⊢
  refine (stripPat_congr (fun j hj e he => ?_)).2 hpatc
  exact flipCol_off G b.c b.s (k + 1) (fun i hi => hoff j (by omega) i (by omega) e he)
end ULHC
