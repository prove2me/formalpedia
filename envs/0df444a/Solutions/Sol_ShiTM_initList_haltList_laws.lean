-- Prove2me | solution 1 for ShiTM.initList_haltList_laws
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T13:55:29.076359+00:00
-- url     : https://prove2.me/submissions/dd6cb491-50ed-40e3-8dd6-da810c7e1467

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Basic API for `Turing.initList` and `Turing.haltList`

`Turing.initList tm s` and `Turing.haltList tm t`
(`Mathlib/Computability/TuringMachine/Computable.lean`) are defined by a raw dependent `dite`
on the stack index, transporting the given list along the equality of indices.  Nothing in
Mathlib records what their projections actually are.  This file supplies the eight defining
equations, bundled into a single statement.

The only nontrivial points are the `stk` projections at the distinguished index: the positive
branch of the `dite` is an `Eq.mpr` transport along `congrArg`, and the equality proof supplied
by `dite` comes from `tm.kDecidableEq`, not from `rfl`.  Instantiating with an explicitly
`rfl`-typed proof via `dif_pos` makes the `congrArg` iota-reduce, so the transport becomes the
identity.
-/

private theorem shiTmapi_initList_l (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₀)) :
    (Turing.initList tm s).l = Option.some tm.main := by
  first
  | (rfl
     done)
  | (simp only [Turing.initList]
     done)
  | (simp [Turing.initList]
     done)

private theorem shiTmapi_initList_var (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₀)) :
    (Turing.initList tm s).var = tm.initialState := by
  first
  | (rfl
     done)
  | (simp only [Turing.initList]
     done)
  | (simp [Turing.initList]
     done)

private theorem shiTmapi_haltList_l (tm : Turing.FinTM2) (t : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm t).l = Option.none := by
  first
  | (rfl
     done)
  | (simp only [Turing.haltList]
     done)
  | (simp [Turing.haltList]
     done)

private theorem shiTmapi_haltList_var (tm : Turing.FinTM2) (t : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm t).var = tm.initialState := by
  first
  | (rfl
     done)
  | (simp only [Turing.haltList]
     done)
  | (simp [Turing.haltList]
     done)

private theorem shiTmapi_initList_stk_self (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₀)) :
    (Turing.initList tm s).stk tm.k₀ = s := by
  have shiTmapi_hinst : tm.kDecidableEq tm.k₀ tm.k₀ = isTrue rfl := by
    first
    | (exact Subsingleton.elim _ _
       done)
    | (exact Subsingleton.elim (tm.kDecidableEq tm.k₀ tm.k₀) (isTrue rfl)
       done)
    | (apply Subsingleton.elim
       done)
  first
  | (simp only [Turing.initList]
     all_goals (exact dif_pos (rfl : tm.k₀ = tm.k₀))
     done)
  | (unfold Turing.initList
     all_goals (exact dif_pos (rfl : tm.k₀ = tm.k₀))
     done)
  | (rw [Turing.initList]
     all_goals (exact dif_pos (rfl : tm.k₀ = tm.k₀))
     done)
  | (simp only [Turing.initList, shiTmapi_hinst]
     done)
  | (simp only [Turing.initList, shiTmapi_hinst, eq_mpr_eq_cast, cast_eq]
     done)
  | (simp only [Turing.initList]
     all_goals (rw [dif_pos (rfl : tm.k₀ = tm.k₀)])
     done)
  | (simp [Turing.initList, shiTmapi_hinst]
     done)
  | (simp [Turing.initList]
     done)
  | (exact dif_pos (rfl : tm.k₀ = tm.k₀)
     done)

private theorem shiTmapi_initList_stk_ne (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₀))
    (k : tm.K) (hk : k ≠ tm.k₀) : (Turing.initList tm s).stk k = [] := by
  first
  | (simp only [Turing.initList]
     all_goals (exact dif_neg hk)
     done)
  | (unfold Turing.initList
     all_goals (exact dif_neg hk)
     done)
  | (rw [Turing.initList]
     all_goals (exact dif_neg hk)
     done)
  | (simp only [Turing.initList, hk]
     done)
  | (simp only [Turing.initList]
     all_goals (rw [dif_neg hk])
     done)
  | (simp [Turing.initList, hk]
     done)
  | (exact dif_neg hk
     done)

private theorem shiTmapi_haltList_stk_self (tm : Turing.FinTM2) (t : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm t).stk tm.k₁ = t := by
  have shiTmapi_hinst : tm.kDecidableEq tm.k₁ tm.k₁ = isTrue rfl := by
    first
    | (exact Subsingleton.elim _ _
       done)
    | (exact Subsingleton.elim (tm.kDecidableEq tm.k₁ tm.k₁) (isTrue rfl)
       done)
    | (apply Subsingleton.elim
       done)
  first
  | (simp only [Turing.haltList]
     all_goals (exact dif_pos (rfl : tm.k₁ = tm.k₁))
     done)
  | (unfold Turing.haltList
     all_goals (exact dif_pos (rfl : tm.k₁ = tm.k₁))
     done)
  | (rw [Turing.haltList]
     all_goals (exact dif_pos (rfl : tm.k₁ = tm.k₁))
     done)
  | (simp only [Turing.haltList, shiTmapi_hinst]
     done)
  | (simp only [Turing.haltList, shiTmapi_hinst, eq_mpr_eq_cast, cast_eq]
     done)
  | (simp only [Turing.haltList]
     all_goals (rw [dif_pos (rfl : tm.k₁ = tm.k₁)])
     done)
  | (simp [Turing.haltList, shiTmapi_hinst]
     done)
  | (simp [Turing.haltList]
     done)
  | (exact dif_pos (rfl : tm.k₁ = tm.k₁)
     done)

private theorem shiTmapi_haltList_stk_ne (tm : Turing.FinTM2) (t : List (tm.Γ tm.k₁))
    (k : tm.K) (hk : k ≠ tm.k₁) : (Turing.haltList tm t).stk k = [] := by
  first
  | (simp only [Turing.haltList]
     all_goals (exact dif_neg hk)
     done)
  | (unfold Turing.haltList
     all_goals (exact dif_neg hk)
     done)
  | (rw [Turing.haltList]
     all_goals (exact dif_neg hk)
     done)
  | (simp only [Turing.haltList, hk]
     done)
  | (simp only [Turing.haltList]
     all_goals (rw [dif_neg hk])
     done)
  | (simp [Turing.haltList, hk]
     done)
  | (exact dif_neg hk
     done)

/--
The eight defining equations of `Turing.initList` and `Turing.haltList`
(`Mathlib/Computability/TuringMachine/Computable.lean`): the initial configuration on input `s`
starts at the main label in the initial state with `s` on the input stack and every other stack
empty, and the halting configuration on output `t` has no label, is in the initial state, and
has `t` on the output stack with every other stack empty.
-/
theorem solution (tm : Turing.FinTM2)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) :
    (Turing.initList tm s).l = Option.some tm.main
      ∧ (Turing.initList tm s).var = tm.initialState
      ∧ (Turing.initList tm s).stk tm.k₀ = s
      ∧ (∀ k : tm.K, k ≠ tm.k₀ → (Turing.initList tm s).stk k = [])
      ∧ (Turing.haltList tm t).l = Option.none
      ∧ (Turing.haltList tm t).var = tm.initialState
      ∧ (Turing.haltList tm t).stk tm.k₁ = t
      ∧ (∀ k : tm.K, k ≠ tm.k₁ → (Turing.haltList tm t).stk k = []) :=
  ⟨shiTmapi_initList_l tm s, shiTmapi_initList_var tm s, shiTmapi_initList_stk_self tm s,
    fun k hk => shiTmapi_initList_stk_ne tm s k hk,
    shiTmapi_haltList_l tm t, shiTmapi_haltList_var tm t, shiTmapi_haltList_stk_self tm t,
    fun k hk => shiTmapi_haltList_stk_ne tm t k hk⟩
