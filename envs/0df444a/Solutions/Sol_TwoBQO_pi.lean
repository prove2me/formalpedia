-- Prove2me | solution 1 for TwoBQO.pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:26.58122+00:00
-- url     : https://prove2.me/submissions/be078382-33b0-4e2f-8551-65b0481e614b

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
public import Theorems.Thm_TwoBQO_comap
public import Theorems.Thm_TwoBQO_prod

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution : ∀ (n : ℕ) (α : Fin n → Type*) (r : ∀ i : Fin n, α i → α i → Prop),
    (∀ i, TwoBQO (r i)) → TwoBQO fun f g : ∀ i, α i => ∀ i, r i (f i) (g i) := by
  intro n
  induction n with
  | zero => intro α r h f; exact ⟨0, 1, 2, by norm_num, by norm_num, fun i => i.elim0⟩
  | succ n ih =>
    intro α r h
    have hpi := ih (fun i => α (Fin.castSucc i)) (fun i => r (Fin.castSucc i))
      fun i => h (Fin.castSucc i)
    have hprod := (h (Fin.last n)).prod hpi
    have key : TwoBQO (fun f g : ∀ i : Fin (n + 1), α i =>
        r (Fin.last n) (f (Fin.last n)) (g (Fin.last n)) ∧
        ∀ i : Fin n, r (Fin.castSucc i) (f (Fin.castSucc i)) (g (Fin.castSucc i))) :=
      hprod.comap fun f : ∀ i : Fin (n + 1), α i => (f (Fin.last n), fun i => f (Fin.castSucc i))
    convert key using 2
    ext f
    constructor
    · intro hall; exact ⟨hall (Fin.last n), fun i => hall (Fin.castSucc i)⟩
    · intro ⟨hlast, hcast⟩ i; exact Fin.lastCases hlast hcast i
end TwoBQO
