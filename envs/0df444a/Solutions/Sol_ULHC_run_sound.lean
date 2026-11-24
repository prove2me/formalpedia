-- Prove2me | solution 1 for ULHC.run_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:21:00.011821+00:00
-- url     : https://prove2.me/submissions/e3a4cb62-9beb-4546-95f2-77de70cdc37b

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Theorems.Thm_ULHC_step_deg2
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cncomp_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G → run V k G = true →
    ∃ H, Deg2 V H ∧ ncomp V H = 1 := by
  intro k
  induction k with
  | zero =>
    intro G hG h
    simp only [run, beq_iff_eq] at h
    exact ⟨G, hG, by rw [← cncomp_eq hG.1]; exact h⟩
  | succ k ih =>
    intro G hG h
    simp only [run] at h
    by_cases h1 : cncomp V G = 1
    · exact ⟨G, hG, by rw [← cncomp_eq hG.1]; exact h1⟩
    · rw [if_neg (by simpa using h1)] at h
      rcases hs : step V G with _ | G'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        exact ih G' (step_deg2 hG hs) h
end ULHC
