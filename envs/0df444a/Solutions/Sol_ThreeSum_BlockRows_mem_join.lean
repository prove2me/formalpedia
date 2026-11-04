-- Prove2me | solution 1 for ThreeSum.BlockRows.mem_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:28.738859+00:00
-- url     : https://prove2.me/submissions/3c4ed19f-983d-4954-93b2-828426e0f10e

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma
end ThreeSum.BlockRows
