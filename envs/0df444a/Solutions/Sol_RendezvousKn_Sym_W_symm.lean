-- Prove2me | solution 1 for RendezvousKn.Sym.W_symm
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:38.135598+00:00
-- url     : https://prove2.me/submissions/03162442-2e69-4875-bed3-d67afa7434da

import Definitions.Def_RendezvousKn_Sym_Model
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open Finset RendezvousKn.Sym

private lemma wait_sym {n : ℕ} (a b : Tactic n) (π : Equiv.Perm (Fin n)) :
    waitTime a b π = waitTime b a π.symm := by
  have hset : univ.filter (fun i : Fin n => π (a i) = b i) =
      univ.filter (fun i : Fin n => π.symm (b i) = a i) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_eq]
    exact eq_comm
  simp only [waitTime, hset]

private lemma W_sym {n : ℕ} (a b : Tactic n) : W a b = W b a := by
  unfold W avgPerm
  congr 1
  apply Finset.sum_bij (fun π _ => π.symm)
  · intro π _; exact mem_univ _
  · intro π _ π' _ h
    have h' := congrArg (fun e : Equiv.Perm (Fin n) => e.symm) h
    simpa only [Equiv.symm_symm] using h'
  · intro π _; exact ⟨π.symm, mem_univ _, rfl⟩
  · intro π _; exact congrArg Nat.cast (wait_sym a b π)

private lemma expected_sym {n : ℕ} (a b : Tactic n → ℝ) : expWait a b = expWait b a := by
  unfold expWait
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  rw [W_sym v u]
  ring

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (∀ τA τB : Tactic n, W τA τB = W τB τA) ∧
    (∀ σ : Tactic n → ℝ, σ ∈ stdSimplex ℝ (Tactic n) →
      expWait σ σ =
        expWait (fun τ => if IsPassive τ then σ τ else 0) (fun τ => if IsPassive τ then σ τ else 0) +
        expWait (fun τ => if IsPassive τ then 0 else σ τ) (fun τ => if IsPassive τ then 0 else σ τ) +
        2 * expWait (fun τ => if IsPassive τ then σ τ else 0)
          (fun τ => if IsPassive τ then 0 else σ τ)) := by
  refine ⟨fun a b => W_sym a b, ?_⟩
  intro σ hσ
  let p : Tactic n → ℝ := fun τ => if IsPassive τ then σ τ else 0
  let a : Tactic n → ℝ := fun τ => if IsPassive τ then 0 else σ τ
  have hσsplit : σ = p + a := by
    funext τ
    dsimp [p,a]
    split_ifs <;> simp
  have hexpand : expWait σ σ = expWait p p + expWait a a + expWait p a + expWait a p := by
    rw [hσsplit]
    simp only [expWait, Pi.add_apply, add_mul, mul_add, sum_add_distrib]
    ring
  change expWait σ σ = expWait p p + expWait a a + 2 * expWait p a
  rw [hexpand, expected_sym a p]
  ring

#print axioms solution
