-- Prove2me | solution 1 for ThreeSum.LayerCounts.mem_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:32.061219+00:00
-- url     : https://prove2.me/submissions/a77c388f-58f8-4901-a58e-b849d392357e

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution {L h : ℕ} {S : Finset (Fin L)} :
    S ∈ vertices L h ↔ S.card = h := by
  simp [vertices]
end ThreeSum.LayerCounts
