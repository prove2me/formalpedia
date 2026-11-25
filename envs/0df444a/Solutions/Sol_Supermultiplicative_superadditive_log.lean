-- Prove2me | solution 1 for Supermultiplicative.superadditive_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:30.725862+00:00
-- url     : https://prove2.me/submissions/32c7e542-5635-4dff-99b3-6ea6c8101570

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
open Supermultiplicative
variable {u : ℕ → ℝ}
namespace Supermultiplicative
theorem _root_.solution (h : Supermultiplicative u) (hpos : ∀ n, 0 < u n) :
    Superadditive fun n ↦ Real.log (u n) := fun m n ↦ by
  rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
  exact Real.log_le_log (mul_pos (hpos m) (hpos n)) (h m n)
end Supermultiplicative
