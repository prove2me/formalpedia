-- Prove2me | solution 1 for ULHC.step_deg2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:18:59.967059+00:00
-- url     : https://prove2.me/submissions/eb412961-900e-4403-94ab-d4cc12031fa0

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Theorems.Thm_ULHC_findT3_some
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_findPath_some
import Theorems.Thm_ULHC_mkBF_cellE
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G G' : Finset Edge} (hG : Deg2 V G)
    (h : step V G = some G') : Deg2 V G' := by
  unfold step at h
  rcases ht : findT3 V G with _ | ⟨d, tf⟩
  · rw [ht] at h
    simp only at h
    rcases hp : findPath V G with _ | ⟨a, L⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨⟨⟨_, hpa, hca, _⟩, _⟩, _⟩ := (findPath_some hG.1 hp).1
      exact deg2_flipCol _ G hG hpa hca
  · rw [ht] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hd, hb, hf, hl1, hl2, _⟩ := findT3_some hG.1 ht
    exact hG.flip (mkBF d tf) hd (mkBF_cellE d tf) hb hf hl1 hl2
end ULHC
