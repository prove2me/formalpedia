-- Prove2me | solution 1 for Subadditive.nearlySubadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:52.754076+00:00
-- url     : https://prove2.me/submissions/d6dea461-eb75-4566-9375-a0b0f943c922

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window
public import Theorems.Thm_NearlySubadditive_of_le_add

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
namespace Subadditive
theorem _root_.solution {u : ℕ → ℝ} (h : Subadditive u) (μ : ℝ) (N : ℕ) :
    NearlySubadditive 0 μ N u :=
  .of_le_add fun m n _ _ ↦ by simpa using h m n
end Subadditive
