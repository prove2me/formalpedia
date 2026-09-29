-- Prove2me | solution 1 for collatz_cycle_gives_syracuse_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:36:56.332824+00:00
-- url     : https://prove2.me/submissions/af30145e-685d-4aff-9ff3-655b239ee497

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep
import Theorems.Thm_collatz_iterate_pos
import Theorems.Thm_collatz_cycle_has_odd
import Theorems.Thm_collatz_reaches_syracuse_iterate

theorem solution (x p : ℕ) (hx : 0 < x) (hp : 0 < p) (hcyc : collatzStep^[p] x = x) :
    ∃ z a k : ℕ, 0 < z ∧ 0 < a ∧ syracuseStep^[a] z = z ∧ collatzStep^[k] x = z := by
  -- an odd point of the classical cycle
  obtain ⟨i, hi⟩ := collatz_cycle_has_odd x p hx hp hcyc
  set y := collatzStep^[i] x with hy
  have hypos : 0 < y := collatz_iterate_pos i x hx
  -- the classical orbit is bounded, since it is periodic
  have hper : Function.IsPeriodicPt collatzStep p x := hcyc
  set B := (Finset.range p).sup (fun j => collatzStep^[j] x) with hB
  have horb : ∀ j, collatzStep^[j] x ≤ B := by
    intro j
    have h1 : collatzStep^[j % p] x = collatzStep^[j] x := hper.iterate_mod_apply j
    rw [← h1]
    exact Finset.le_sup (f := fun j => collatzStep^[j] x) (Finset.mem_range.mpr (Nat.mod_lt _ hp))
  -- every Syracuse iterate of y is a classical iterate of x, hence bounded
  have hTb : ∀ t, syracuseStep^[t] y ≤ B := by
    intro t
    obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate y hi t
    rw [← hM, hy, ← Function.iterate_add_apply]
    exact horb (M + i)
  have hTpos : ∀ t, 0 < syracuseStep^[t] y := by
    intro t
    induction t with
    | zero => simpa using hypos
    | succ n _ =>
      rw [Function.iterate_succ_apply']
      exact Nat.ordCompl_pos 2 (by omega)
  -- pigeonhole: the Syracuse orbit of y cannot be injective into a finite range
  obtain ⟨s, t, hst, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun t : ℕ => (⟨syracuseStep^[t] y, by
      have := hTb t; omega⟩ : Fin (B + 1)))
  have heq' : syracuseStep^[s] y = syracuseStep^[t] y := by
    simpa using congrArg Fin.val heq
  -- order them and read off a genuine Syracuse cycle
  rcases Nat.lt_or_ge s t with h | h
  · obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate y hi s
    refine ⟨syracuseStep^[s] y, t - s, M + i, hTpos s, by omega, ?_, ?_⟩
    · rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h)]
      exact heq'.symm
    · rw [Function.iterate_add_apply]
      exact hM
  · have hts : t < s := by omega
    obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate y hi t
    refine ⟨syracuseStep^[t] y, s - t, M + i, hTpos t, by omega, ?_, ?_⟩
    · rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hts)]
      exact heq'
    · rw [Function.iterate_add_apply]
      exact hM
