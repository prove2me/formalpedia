-- Prove2me | solution 1 for Preorder.IsRegularSeq.exists_strictMono_dominating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:55.18351+00:00
-- url     : https://prove2.me/submissions/87f2ec1a-9474-499e-b978-b11822958b2e

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
section
@[expose] public section
open Set Preorder
noncomputable section
namespace PairSeq
end PairSeq
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
private theorem exists_strictMono_of_greedy {P : ℕ → ℕ → Prop}
    (hbuild : ∀ start i : ℕ, ∃ j, start < j ∧ P i j) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, P i (e i) := by
  let e : ℕ → ℕ := fun i =>
    Nat.rec (motive := fun _ => ℕ) (hbuild 0 0).choose
      (fun n prev => (hbuild prev (n + 1)).choose) i
  have he0 : e 0 = (hbuild 0 0).choose := rfl
  have hesucc : ∀ n, e (n + 1) = (hbuild (e n) (n + 1)).choose := fun n => rfl
  have hP0 : P 0 (e 0) := he0 ▸ (hbuild 0 0).choose_spec.2
  have hPsucc : ∀ n, P (n + 1) (e (n + 1)) := fun n =>
    (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.2
  have hlt : ∀ n, e n < e (n + 1) := fun n => (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.1
  refine ⟨e, strictMono_nat_of_lt_succ hlt, fun i => ?_⟩
  cases i with
  | zero => exact hP0
  | succ n => exact hPsucc n
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
namespace Preorder.IsRegularSeq
theorem _root_.solution {Q : Type*} {le : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq le f) (n : ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, n ≤ e i ∧ le (f i) (f (e i)) := by
  apply exists_strictMono_of_greedy (P := fun i j => n ≤ j ∧ le (f i) (f j))
  intro start i
  obtain ⟨j, hj_mem, hj_gt⟩ := (hf i).exists_gt (max start n)
  exact ⟨j, lt_of_le_of_lt (le_max_left _ _) hj_gt,
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hj_gt), hj_mem⟩
end Preorder.IsRegularSeq
