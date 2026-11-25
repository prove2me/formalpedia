-- Prove2me | solution 1 for Superadditive.subadditive_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:13.619269+00:00
-- url     : https://prove2.me/submissions/a4b27d56-31fe-40eb-b307-d261b78bc1a5

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
namespace Superadditive
theorem _root_.solution {u : ℕ → ℝ} (h : Superadditive u) :
    Subadditive fun n ↦ -u n := fun m n ↦ by linarith [h m n]
end Superadditive
