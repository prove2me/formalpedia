-- Prove2me | solution 1 for WindowedMatching.price_mono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:56:59.620199+00:00
-- url     : https://prove2.me/submissions/9045b55c-eb43-4293-a6f5-a57c99105c95

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WMprice
open WindowedMatching

variable {n : ℕ}

lemma critical_p (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).p = st.p := by
  unfold critical
  split
  · rfl
  · dsimp only
    split_ifs <;> rfl

lemma bid_mono (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n)
    (s : Fin n) : st.p s ≤ (bid d v tie k st).p s := by
  unfold bid
  dsimp only
  split_ifs with h
  · dsimp only
    by_cases hs : s = tie k st.S (margins d v k st)
    · rw [hs, Function.update_self]
      rw [← hs] at h ⊢
      unfold margins at h
      split_ifs at h
      · linarith
      · exact absurd h (lt_irrefl 0)
    · rw [Function.update_of_ne hs]
  · exact le_refl _

lemma arrive_mono (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n)
    (s : Fin n) (hs : s ≠ k) : st.p s ≤ (arrive d v tie k st).p s := by
  unfold arrive
  have : (addVertex k st).p s = st.p s := by
    simp only [addVertex, Function.update_of_ne hs]
  rw [← this]
  exact bid_mono d v tie k _ s

lemma period_p (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (ω : Fin n → Bool)
    (t : ℕ) (st : State n) :
    (period d v tie ω t st).p = (if h : t < n then arrive d v tie ⟨t, h⟩ st else st).p := by
  unfold period
  dsimp only
  split_ifs <;> first | rfl | exact critical_p _ _ _

lemma period_mono (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (ω : Fin n → Bool)
    (t : ℕ) (st : State n) (s : Fin n) (hst : (s : ℕ) ≠ t) :
    st.p s ≤ (period d v tie ω t st).p s := by
  rw [period_p]
  split_ifs with h
  · exact arrive_mono d v tie _ st s (fun e => hst (by rw [e]))
  · exact le_refl _

end Aux_WMprice

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (s : Fin n) (t₁ t₂ : ℕ) (hs : (s : ℕ) < t₁)
    (ht : t₁ ≤ t₂) :
    (stateAfter d v tie ω t₁).p s ≤ (stateAfter d v tie ω t₂).p s := by
  induction t₂, ht using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    refine le_trans ih ?_
    show (stateAfter d v tie ω m).p s ≤ (period d v tie ω m (stateAfter d v tie ω m)).p s
    exact Aux_WMprice.period_mono d v tie ω m _ s (by omega)
