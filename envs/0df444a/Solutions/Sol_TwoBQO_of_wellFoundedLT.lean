-- Prove2me | solution 1 for TwoBQO.of_wellFoundedLT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:05.318475+00:00
-- url     : https://prove2.me/submissions/2b20d624-aef5-4837-9a6a-06b575dae6cc

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Theorems.Thm_TwoBQO_iff_noBad

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    TwoBQO (α := α) (· ≤ ·) := by
  rw [TwoBQO.iff_noBad]
  intro ⟨f, hbad⟩
  have hstrict : ∀ n, f (n + 1) (n + 2) (Nat.lt_succ_self _) < f n (n + 1) (Nat.lt_succ_self _) :=
    fun n => not_le.mp (hbad n (n + 1) (n + 2) (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1)))
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
    fun n => f n (n + 1) (Nat.lt_succ_self n)
  exact hn (hstrict n)
end TwoBQO
