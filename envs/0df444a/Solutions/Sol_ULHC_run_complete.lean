-- Prove2me | solution 1 for ULHC.run_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:46:31.696363+00:00
-- url     : https://prove2.me/submissions/a4734128-a940-4b8b-b6a2-7b073970d247

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_step_decrease
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cncomp_eq
import Theorems.Thm_ULHC_step_deg2
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hPC : PathComplete V)
include hs x0 hconn hPC
namespace ULHC
theorem _root_.solution (hne : V.Nonempty) : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G →
    Mz V G < k → run V k G = true := by
  intro k
  induction k with
  | zero => intro G _ h; omega
  | succ k ih =>
    intro G hG hk
    simp only [run]
    by_cases h1 : cncomp V G = 1
    · simp [h1]
    · rw [if_neg (by simpa using h1)]
      have hpos : 1 ≤ ncomp V G :=
        Finset.card_pos.2 (hne.image _)
      have h2 : 2 ≤ ncomp V G := by
        rw [cncomp_eq hG.1] at h1
        omega
      obtain ⟨G', hs', hlt⟩ := step_decrease hs x0 hconn hPC hG h2
      rw [hs']
      exact ih G' (step_deg2 hG hs') (by omega)
end ULHC
