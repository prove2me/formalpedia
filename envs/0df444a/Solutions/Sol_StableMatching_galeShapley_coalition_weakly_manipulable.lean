-- Prove2me | solution 1 for StableMatching.galeShapley_coalition_weakly_manipulable
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:09:18.942024+00:00
-- url     : https://prove2.me/submissions/58675b15-6d42-403b-b269-b5817022d093

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

set_option autoImplicit false

open StableMatching

namespace StableMatching.GSEx

/-! ### General tools for running Gale–Shapley on explicit states -/

theorem state_eq {n : ℕ} (s t : GSState n) (h1 : ∀ m, s.next m = t.next m)
    (h2 : ∀ w, s.fiance w = t.fiance w) : s = t := by
  cases s; cases t
  simp only [GSState.mk.injEq]
  exact ⟨funext h1, funext h2⟩

theorem gsRun_zero {n : ℕ} (I : Instance n) : I.gsRun 0 = GSState.init n := rfl

theorem gsRun_succ {n : ℕ} (I : Instance n) (k : ℕ) :
    I.gsRun (k + 1) = I.gsRound (I.gsRun k) :=
  Function.iterate_succ_apply' _ _ _

/-- If the run reaches a fixpoint `s` of `gsRound` within `n ^ 2` rounds, the final state is `s`. -/
theorem galeShapley_eq {n : ℕ} (I : Instance n) (s : GSState n) (k : ℕ) (hk : k ≤ n ^ 2)
    (h : I.gsRun k = s) (hfix : I.gsRound s = s) : I.galeShapley = s := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
  unfold Instance.galeShapley Instance.gsRun at *
  rw [hj, add_comm, Function.iterate_add_apply, h]
  exact Function.iterate_fixed hfix j

theorem outcome_of {n : ℕ} (I : Instance n) (s : GSState n) (μ : Matching n)
    (hs : I.galeShapley = s) (h : ∀ m, s.fiance (μ m) = some m) : I.IsGSOutcome μ := by
  intro m; rw [hs]; exact h m

/-! ### Permutations of `Fin 3`, named by their value tables -/

def p021 : Fin 3 ≃ Fin 3 := ⟨![0,2,1], ![0,2,1], by decide, by decide⟩
def p102 : Fin 3 ≃ Fin 3 := ⟨![1,0,2], ![1,0,2], by decide, by decide⟩
def p120 : Fin 3 ≃ Fin 3 := ⟨![1,2,0], ![2,0,1], by decide, by decide⟩
def p210 : Fin 3 ≃ Fin 3 := ⟨![2,1,0], ![2,1,0], by decide, by decide⟩
def p201 : Fin 3 ≃ Fin 3 := ⟨![2,0,1], ![1,2,0], by decide, by decide⟩
def p012 : Fin 3 ≃ Fin 3 := ⟨![0,1,2], ![0,1,2], by decide, by decide⟩

/-! ### The instance

True preferences (ranks): `MR = [[2,0,1],[1,0,2],[0,1,2]]`, `WR = [[2,0,1],[1,2,0],[0,2,1]]`.
The coalition is `C = {0, 1}`; man `0` reports `[0,2,1]`, man `1` reports his true list. -/

def Ic : Instance 3 := ⟨![p201, p102, p012], ![p201, p120, p021]⟩
def Ic' : Instance 3 := ⟨Function.update Ic.manRank 0 p021, Ic.womanRank⟩

/-! Run of `Ic` (true preferences). -/
def sA1 : GSState 3 := ⟨![1,1,1], ![some 2, some 0, none]⟩
def sA2 : GSState 3 := ⟨![1,2,1], ![some 1, some 0, none]⟩
def sA3 : GSState 3 := ⟨![1,2,2], ![some 1, some 2, none]⟩
def sA4 : GSState 3 := ⟨![2,2,2], ![some 1, some 2, some 0]⟩

theorem Ic_1 : Ic.gsRound (GSState.init 3) = sA1 := state_eq _ _ (by decide) (by decide)
theorem Ic_2 : Ic.gsRound sA1 = sA2 := state_eq _ _ (by decide) (by decide)
theorem Ic_3 : Ic.gsRound sA2 = sA3 := state_eq _ _ (by decide) (by decide)
theorem Ic_4 : Ic.gsRound sA3 = sA4 := state_eq _ _ (by decide) (by decide)
theorem Ic_fix : Ic.gsRound sA4 = sA4 := state_eq _ _ (by decide) (by decide)

theorem Ic_run : Ic.gsRun 4 = sA4 := by
  rw [gsRun_succ, gsRun_succ, gsRun_succ, gsRun_succ, gsRun_zero, Ic_1, Ic_2, Ic_3, Ic_4]

theorem Ic_out : Ic.IsGSOutcome p201 :=
  outcome_of _ _ _ (galeShapley_eq _ _ 4 (by norm_num) Ic_run Ic_fix) (by decide)

/-! Run of `Ic'` (the coalition misreports). -/
def sB1 : GSState 3 := ⟨![1,1,1], ![some 2, some 1, none]⟩
def sB2 : GSState 3 := ⟨![2,1,1], ![some 2, some 1, some 0]⟩

theorem Ic'_1 : Ic'.gsRound (GSState.init 3) = sB1 := state_eq _ _ (by decide) (by decide)
theorem Ic'_2 : Ic'.gsRound sB1 = sB2 := state_eq _ _ (by decide) (by decide)
theorem Ic'_fix : Ic'.gsRound sB2 = sB2 := state_eq _ _ (by decide) (by decide)

theorem Ic'_run : Ic'.gsRun 2 = sB2 := by
  rw [gsRun_succ, gsRun_succ, gsRun_zero, Ic'_1, Ic'_2]

theorem Ic'_out : Ic'.IsGSOutcome p210 :=
  outcome_of _ _ _ (galeShapley_eq _ _ 2 (by norm_num) Ic'_run Ic'_fix) (by decide)

/-! Deviation and preference facts. -/

theorem Ic_dev : Ic.MenDeviation Ic' {0, 1} := by
  refine ⟨?_, rfl⟩
  intro m hm
  have h0 : m ≠ 0 := fun h => hm (by simp [h])
  exact Function.update_of_ne h0 _ _

theorem Ic_weak : ∀ m ∈ ({0, 1} : Finset (Fin 3)), p210 m = p201 m ∨ Ic.manPrefers m (p210 m) (p201 m) := by
  unfold Instance.manPrefers
  decide

theorem Ic_strict : ∃ m ∈ ({0, 1} : Finset (Fin 3)), Ic.manPrefers m (p210 m) (p201 m) := by
  unfold Instance.manPrefers
  decide

end StableMatching.GSEx

open StableMatching.GSEx in
theorem solution :
    ∃ (n : ℕ) (I I' : Instance n) (C : Finset (Fin n)) (μ μ' : Matching n),
      I.MenDeviation I' C ∧ I.IsGSOutcome μ ∧ I'.IsGSOutcome μ' ∧
      (∀ m ∈ C, μ' m = μ m ∨ I.manPrefers m (μ' m) (μ m)) ∧
      ∃ m ∈ C, I.manPrefers m (μ' m) (μ m) :=
  ⟨3, Ic, Ic', {0, 1}, p201, p210, Ic_dev, Ic_out, Ic'_out, Ic_weak, Ic_strict⟩
