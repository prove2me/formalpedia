-- Prove2me | solution 1 for WindowedMatching.virtual_run_coin_free
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:07:42.930834+00:00
-- url     : https://prove2.me/submissions/8d1f38ae-3803-446c-9332-8f851097aa5f

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WMcoin
open WindowedMatching

def R {n : ℕ} (a b : State n) : Prop :=
  a.S = b.S ∧ a.B = b.B ∧ a.p = b.p ∧ a.m = b.m ∧ a.q = b.q

theorem arrive_R {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n)
    {a b : State n} (h : R a b) : R (arrive d v tie k a) (arrive d v tie k b) := by
  obtain ⟨S, B, p, m, q, st, f⟩ := a
  obtain ⟨S', B', p', m', q', st', f'⟩ := b
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  unfold R arrive bid addVertex margins
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem critical_R {n : ℕ} (ω ω' : Fin n → Bool) (k : Fin n)
    {a b : State n} (h : R a b) : R (critical ω k a) (critical ω' k b) := by
  obtain ⟨S, B, p, m, q, st, f⟩ := a
  obtain ⟨S', B', p', m', q', st', f'⟩ := b
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  unfold R critical
  dsimp only
  cases hmk : m k with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some l =>
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Aux_WMcoin

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω ω' : Fin n → Bool) (t : ℕ) :
    (stateAfter d v tie ω t).S = (stateAfter d v tie ω' t).S ∧
    (stateAfter d v tie ω t).B = (stateAfter d v tie ω' t).B ∧
    (stateAfter d v tie ω t).p = (stateAfter d v tie ω' t).p ∧
    (stateAfter d v tie ω t).m = (stateAfter d v tie ω' t).m ∧
    (stateAfter d v tie ω t).q = (stateAfter d v tie ω' t).q := by
  have key : ∀ t, Aux_WMcoin.R (stateAfter d v tie ω t) (stateAfter d v tie ω' t) := by
    intro t
    induction t with
    | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | succ t ih =>
      simp only [stateAfter]
      unfold period
      dsimp only
      split_ifs <;>
        first
        | exact Aux_WMcoin.critical_R _ _ _ (Aux_WMcoin.arrive_R _ _ _ _ ih)
        | exact Aux_WMcoin.critical_R _ _ _ ih
        | exact Aux_WMcoin.arrive_R _ _ _ _ ih
        | exact ih
  exact key t
