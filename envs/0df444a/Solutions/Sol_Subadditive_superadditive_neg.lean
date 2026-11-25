-- Prove2me | solution 1 for Subadditive.superadditive_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:23.221832+00:00
-- url     : https://prove2.me/submissions/33f6b1d6-2026-4e69-bdef-3c8e8eb221ed

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
namespace Subadditive
theorem _root_.solution {u : ℕ → ℝ} (h : Subadditive u) :
    Superadditive fun n ↦ -u n := fun m n ↦ by linarith [h m n]
end Subadditive
