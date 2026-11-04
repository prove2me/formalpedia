-- Prove2me | solution 1 for ThreeSum.LayerCounts.mem_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:45.124454+00:00
-- url     : https://prove2.me/submissions/4a470ede-104e-45e4-9891-a90fbc0940fe

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices

set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset
namespace ThreeSum.LayerCounts
theorem _root_.solution {L h : ℕ} {p : Finset (Fin L) × Finset (Fin L)} :
    p ∈ edgeSet L h ↔ p.1.card = h ∧ p.2.card = h ∧ Disjoint p.1 p.2 := by
  simp [edgeSet, and_assoc]
end ThreeSum.LayerCounts
