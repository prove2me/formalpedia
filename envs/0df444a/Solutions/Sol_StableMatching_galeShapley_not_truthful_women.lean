-- Prove2me | solution 1 for StableMatching.galeShapley_not_truthful_women
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:07:34.065322+00:00
-- url     : https://prove2.me/submissions/c3a42bd3-dd6e-42ff-aab1-9f2cffeca46e

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
def p120 : Fin 3 ≃ Fin 3 := ⟨![1,2,0], ![2,0,1], by decide, by decide⟩
def p210 : Fin 3 ≃ Fin 3 := ⟨![2,1,0], ![2,1,0], by decide, by decide⟩
def p201 : Fin 3 ≃ Fin 3 := ⟨![2,0,1], ![1,2,0], by decide, by decide⟩
def p012 : Fin 3 ≃ Fin 3 := ⟨![0,1,2], ![0,1,2], by decide, by decide⟩

/-! ### The instance

True preferences (ranks): `MR = [[0,2,1],[1,2,0],[2,1,0]]`, `WR = [[2,0,1],[2,1,0],[0,1,2]]`.
Woman `2` misreports her list as `WR'[2] = [0,2,1]`. -/

def Iw : Instance 3 := ⟨![p021, p120, p210], ![p201, p210, p012]⟩
def Iw' : Instance 3 := ⟨Iw.manRank, Function.update Iw.womanRank 2 p021⟩

/-! Run of `Iw` (true preferences). -/
def sA1 : GSState 3 := ⟨![1,1,1], ![some 0, none, some 1]⟩
def sA2 : GSState 3 := ⟨![1,1,2], ![some 0, some 2, some 1]⟩

theorem Iw_1 : Iw.gsRound (GSState.init 3) = sA1 := state_eq _ _ (by decide) (by decide)
theorem Iw_2 : Iw.gsRound sA1 = sA2 := state_eq _ _ (by decide) (by decide)
theorem Iw_fix : Iw.gsRound sA2 = sA2 := state_eq _ _ (by decide) (by decide)

theorem Iw_run : Iw.gsRun 2 = sA2 := by
  rw [gsRun_succ, gsRun_succ, gsRun_zero, Iw_1, Iw_2]

theorem Iw_out : Iw.IsGSOutcome p021 :=
  outcome_of _ _ _ (galeShapley_eq _ _ 2 (by norm_num) Iw_run Iw_fix) (by decide)

/-! Run of `Iw'` (woman `2` lies). -/
def sB1 : GSState 3 := ⟨![1,1,1], ![some 0, none, some 2]⟩
def sB2 : GSState 3 := ⟨![1,2,1], ![some 1, none, some 2]⟩
def sB3 : GSState 3 := ⟨![2,2,1], ![some 1, none, some 0]⟩
def sB4 : GSState 3 := ⟨![2,2,2], ![some 1, some 2, some 0]⟩

theorem Iw'_1 : Iw'.gsRound (GSState.init 3) = sB1 := state_eq _ _ (by decide) (by decide)
theorem Iw'_2 : Iw'.gsRound sB1 = sB2 := state_eq _ _ (by decide) (by decide)
theorem Iw'_3 : Iw'.gsRound sB2 = sB3 := state_eq _ _ (by decide) (by decide)
theorem Iw'_4 : Iw'.gsRound sB3 = sB4 := state_eq _ _ (by decide) (by decide)
theorem Iw'_fix : Iw'.gsRound sB4 = sB4 := state_eq _ _ (by decide) (by decide)

theorem Iw'_run : Iw'.gsRun 4 = sB4 := by
  rw [gsRun_succ, gsRun_succ, gsRun_succ, gsRun_succ, gsRun_zero, Iw'_1, Iw'_2, Iw'_3, Iw'_4]

theorem Iw'_out : Iw'.IsGSOutcome p201 :=
  outcome_of _ _ _ (galeShapley_eq _ _ 4 (by norm_num) Iw'_run Iw'_fix) (by decide)

/-! Deviation and preference facts. -/

theorem Iw_dev : Iw.WomanDeviation Iw' 2 := by
  refine ⟨rfl, ?_⟩
  intro w' hw'
  exact Function.update_of_ne hw' _ _

theorem Iw_pref : Iw.womanPrefers 2 (p201.symm 2) (p021.symm 2) := by
  unfold Instance.womanPrefers
  decide

end StableMatching.GSEx

open StableMatching.GSEx in
theorem solution :
    ∃ (n : ℕ) (I I' : Instance n) (w : Fin n) (μ μ' : Matching n),
      I.WomanDeviation I' w ∧ I.IsGSOutcome μ ∧ I'.IsGSOutcome μ' ∧
      I.womanPrefers w (μ'.symm w) (μ.symm w) :=
  ⟨3, Iw, Iw', 2, p021, p201, Iw_dev, Iw_out, Iw'_out, Iw_pref⟩
