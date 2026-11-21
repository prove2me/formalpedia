-- Prove2me | solution 1 for WindowedMatching.margin_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:29:31.552409+00:00
-- url     : https://prove2.me/submissions/3dcc86fc-6b65-48e3-a647-8995f887a532

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WindowedMatching_margin_ge

open WindowedMatching

variable {n : ℕ}

theorem crit_q (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).q = st.q := by
  unfold critical
  split
  · rfl
  · dsimp only
    split_ifs <;> rfl

theorem crit_mem (ω : Fin n → Bool) (k : Fin n) (st : State n) (x : Fin n) (hxk : x ≠ k)
    (hx : x ∈ st.S) : x ∈ (critical ω k st).S := by
  unfold critical
  split
  · exact hx
  · dsimp only
    split_ifs
    · exact Finset.mem_erase.mpr ⟨hxk, hx⟩
    · exact Finset.mem_erase.mpr ⟨hxk, hx⟩

theorem bid_q (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (bid d v tie k st).q
      = Function.update st.q k (margins d v k st (tie k st.S (margins d v k st))) := by
  unfold bid
  dsimp only
  split_ifs <;> rfl

theorem bid_S (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (bid d v tie k st).S = st.S := by
  unfold bid
  dsimp only
  split_ifs <;> rfl

theorem arrive_S (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (arrive d v tie k st).S = insert k st.S := by
  unfold arrive
  rw [bid_S]
  rfl

theorem S_inv (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω : Fin n → Bool) : ∀ t : ℕ, ∀ i : Fin n, i.val < t → t ≤ i.val + d →
      i ∈ (stateAfter d v tie ω t).S := by
  intro t
  induction t with
  | zero => intro i h1 _; omega
  | succ t ih =>
    intro i h1 h2
    obtain ⟨st1, hst1⟩ : ∃ x, x = (if h : t < n then
        arrive d v tie ⟨t, h⟩ (stateAfter d v tie ω t) else stateAfter d v tie ω t) := ⟨_, rfl⟩
    have hi1 : i ∈ st1.S := by
      rw [hst1]
      by_cases h : t < n
      · rw [dif_pos h, arrive_S]
        by_cases hit : i.val = t
        · have : i = ⟨t, h⟩ := Fin.ext hit
          rw [this]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ih i (by omega) (by omega))
      · rw [dif_neg h]
        have := i.isLt
        exact ih i (by omega) (by omega)
    have hper : stateAfter d v tie ω (t + 1)
        = if h : d ≤ t ∧ t - d < n then critical ω ⟨t - d, h.2⟩ st1 else st1 := by
      subst hst1; rfl
    rw [hper]
    by_cases h2 : d ≤ t ∧ t - d < n
    · rw [dif_pos h2]
      refine crit_mem ω _ st1 i ?_ hi1
      intro h
      have : i.val = t - d := congrArg Fin.val h
      omega
    · rw [dif_neg h2]
      exact hi1

end Aux_WindowedMatching_margin_ge

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (i j : Fin n) (hij : i < j)
    (hj : (j : ℕ) ≤ i + d) :
    v s(i, j) - (stateAfter d v tie ω j).p i ≤ (stateAfter d v tie ω (j + 1)).q j := by
  have hij' : (i : ℕ) < j := hij
  have hS := Aux_WindowedMatching_margin_ge.S_inv d hd v tie ω j i hij' hj
  obtain ⟨st, hst⟩ : ∃ x, x = stateAfter d v tie ω j := ⟨_, rfl⟩
  rw [← hst] at hS ⊢
  have hstep : stateAfter d v tie ω (j + 1) = period d v tie ω j st := by
    subst hst; rfl
  have hq : (period d v tie ω j st).q = (arrive d v tie j st).q := by
    unfold period
    dsimp only
    rw [dif_pos j.isLt]
    by_cases h2 : d ≤ (j : ℕ) ∧ (j : ℕ) - d < n
    · rw [dif_pos h2, Aux_WindowedMatching_margin_ge.crit_q]
      all_goals rfl
    · rw [dif_neg h2]
      all_goals rfl
  rw [hstep, hq]
  unfold arrive
  rw [Aux_WindowedMatching_margin_ge.bid_q, Function.update_self]
  have hiS : i ∈ (addVertex j st).S := Finset.mem_insert_of_mem hS
  have hmx := (hTie j (addVertex j st).S (margins d v j (addVertex j st)) ⟨i, hiS⟩).2 i hiS
  refine le_trans (le_of_eq ?_) hmx
  have hne : i ≠ j := ne_of_lt hij
  have hadj : (windowGraph n d).Adj i j := by
    refine ⟨hne, ?_⟩
    rw [abs_le]
    constructor <;> omega
  show v s(i, j) - st.p i
    = (if i ∈ (addVertex j st).S then onlineWeight d v i j - (addVertex j st).p i else 0)
  rw [if_pos hiS]
  unfold onlineWeight
  rw [if_pos hadj]
  show v s(i, j) - st.p i = v s(i, j) - Function.update st.p j 0 i
  rw [Function.update_of_ne hne]
