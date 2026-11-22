-- Prove2me | solution 1 for ShiTM.exists_stepAux_stack_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T18:07:50.74738+00:00
-- url     : https://prove2.me/submissions/ea70826f-21ec-4fd9-a24f-3dae88f47ebf

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

/-!
A `TM2` stack machine grows its total stack size by at most a constant per `step`.

`Turing.TM2.stepAux` recurses through an entire `Stmt` tree inside one `step`, so a single
step can `push` several times; but the tree is fixed and finite, so the growth is bounded by
a constant depending only on the statement.  Since a bundled machine has finitely many
labels (`Fintype Λ`), one constant works for the whole machine, uniformly in the label, the
internal state and the stack contents.  This is the missing ingredient that makes the
time-bound arithmetic for a composition of polynomial-time `TM2`s non-vacuous: it bounds the
length of a machine's output in terms of its running time.
-/

/-- Total stack size after a (dependent) `Function.update`: split off the updated index.
This is the key computation; `Finset.sum_update_of_mem` does *not* apply, because
`S : ∀ k, List (Γ k)` is a dependent function, so `fun k => (Function.update S k₀ x k).length`
is not of the form `Function.update g k₀ n` for any `g : K → ℕ`. -/
private theorem shiGrow_sum_update {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
    (S : ∀ k, List (Γ k)) (k₀ : K) (x : List (Γ k₀)) :
    ∑ k, ((Function.update S k₀ x) k).length
      = (∑ k ∈ Finset.univ.erase k₀, (S k).length) + x.length := by
  have h : ∀ k ∈ Finset.univ.erase k₀,
      ((Function.update S k₀ x) k).length = (S k).length := by
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h2 : (∑ k ∈ Finset.univ.erase k₀, ((Function.update S k₀ x) k).length)
      = ∑ k ∈ Finset.univ.erase k₀, (S k).length := Finset.sum_congr rfl h
  rw [← Finset.sum_erase_add Finset.univ
      (fun k => ((Function.update S k₀ x) k).length) (Finset.mem_univ k₀)]
  simp only [Function.update_self]
  rw [h2]

/-- Split the total stack size at a distinguished index. -/
private theorem shiGrow_sum_erase_split {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
    (S : ∀ k, List (Γ k)) (k₀ : K) :
    ∑ k, (S k).length = (∑ k ∈ Finset.univ.erase k₀, (S k).length) + (S k₀).length :=
  (Finset.sum_erase_add Finset.univ (fun k => (S k).length) (Finset.mem_univ k₀)).symm

/-- **Step A.**  For a single statement `q`, the total stack size after running `q` exceeds the
total stack size before by at most a constant depending only on `q`.  Proved by induction on
the statement tree: `push` adds one, `pop` can only shrink, `peek`/`load` leave the stacks
alone, `branch` takes the max of the two branches, `goto`/`halt` add nothing. -/
private theorem shiGrow_stepAux_bound {K : Type} [DecidableEq K] [Fintype K]
    {Γ : K → Type} {Λ σ : Type} (q : Turing.TM2.Stmt Γ Λ σ) :
    ∃ c : ℕ, ∀ (v : σ) (S : ∀ k, List (Γ k)),
      ∑ k, ((Turing.TM2.stepAux q v S).stk k).length ≤ (∑ k, (S k).length) + c := by
  induction q with
  | push k₀ f q ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + 1, fun v S => ?_⟩
    have hupd : ∑ k, ((Function.update S k₀ (f v :: S k₀)) k).length
        = (∑ k, (S k).length) + 1 := by
      rw [shiGrow_sum_update, List.length_cons, shiGrow_sum_erase_split S k₀]
      omega
    have h1 := hc v (Function.update S k₀ (f v :: S k₀))
    rw [Turing.TM2.stepAux.eq_1]
    omega
  | peek k₀ f q ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c, fun v S => ?_⟩
    rw [Turing.TM2.stepAux.eq_2]
    exact hc _ _
  | pop k₀ f q ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c, fun v S => ?_⟩
    have hupd : ∑ k, ((Function.update S k₀ (S k₀).tail) k).length
        ≤ ∑ k, (S k).length := by
      rw [shiGrow_sum_update, List.length_tail, shiGrow_sum_erase_split S k₀]
      omega
    have h1 := hc (f v (S k₀).head?) (Function.update S k₀ (S k₀).tail)
    rw [Turing.TM2.stepAux.eq_3]
    omega
  | load a q ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c, fun v S => ?_⟩
    rw [Turing.TM2.stepAux.eq_4]
    exact hc _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    obtain ⟨c₁, hb₁⟩ := ih₁
    obtain ⟨c₂, hb₂⟩ := ih₂
    refine ⟨max c₁ c₂, fun v S => ?_⟩
    rw [Turing.TM2.stepAux.eq_5]
    rcases Bool.eq_false_or_eq_true (f v) with hfv | hfv
    · rw [hfv]
      first
        | (rw [cond_true];
           exact le_trans (hb₁ v S) (Nat.add_le_add_left (le_max_left c₁ c₂) _);
           done)
        | (exact le_trans (hb₁ v S) (Nat.add_le_add_left (le_max_left c₁ c₂) _);
           done)
        | (simp only [Bool.cond_true];
           exact le_trans (hb₁ v S) (Nat.add_le_add_left (le_max_left c₁ c₂) _);
           done)
    · rw [hfv]
      first
        | (rw [cond_false];
           exact le_trans (hb₂ v S) (Nat.add_le_add_left (le_max_right c₁ c₂) _);
           done)
        | (exact le_trans (hb₂ v S) (Nat.add_le_add_left (le_max_right c₁ c₂) _);
           done)
        | (simp only [Bool.cond_false];
           exact le_trans (hb₂ v S) (Nat.add_le_add_left (le_max_right c₁ c₂) _);
           done)
  | goto f =>
    refine ⟨0, fun v S => ?_⟩
    first
      | (simp; done)
      | (simp only [Turing.TM2.stepAux.eq_6, Nat.add_zero]; exact le_refl _; done)
  | halt =>
    refine ⟨0, fun v S => ?_⟩
    first
      | (simp; done)
      | (simp only [Turing.TM2.stepAux.eq_7, Nat.add_zero]; exact le_refl _; done)

/-- **A `TM2` machine's total stack size grows by at most a constant per step.**

For any `TM2` program `M` over finitely many stacks and finitely many labels there is a
constant `c` such that executing the statement at *any* label, from *any* internal state and
*any* stack contents, increases the total stack size by at most `c`.  The constant is uniform
in the label `l`, the state `v` and the stacks `S`; that uniformity is the whole content of
the statement, and it is what lets one conclude by induction that a machine run for `t` steps
from an input of length `n` has total stack size at most `n + c * t` -- in particular its
output is polynomially bounded, which is what makes the time bounds for a composition of
polynomial-time `TM2`s non-vacuous.

Note that one `Turing.TM2.step` runs `Turing.TM2.stepAux` through an entire `Stmt` tree, so a
single step may `push` many times; `c` absorbs the largest number of `push` nodes on any root
path of any of the finitely many statements `M l`. -/
theorem solution {K : Type} [DecidableEq K] [Fintype K]
    {Γ : K → Type} {Λ σ : Type} [Fintype Λ] (M : Λ → Turing.TM2.Stmt Γ Λ σ) :
    ∃ c : ℕ, ∀ (l : Λ) (v : σ) (S : ∀ k, List (Γ k)),
      ∑ k, ((Turing.TM2.stepAux (M l) v S).stk k).length
        ≤ (∑ k, (S k).length) + c := by
  refine ⟨Finset.univ.sup fun l => (shiGrow_stepAux_bound (M l)).choose, fun l v S => ?_⟩
  refine le_trans ((shiGrow_stepAux_bound (M l)).choose_spec v S) ?_
  exact Nat.add_le_add_left
    (Finset.le_sup (f := fun l => (shiGrow_stepAux_bound (M l)).choose) (Finset.mem_univ l)) _
