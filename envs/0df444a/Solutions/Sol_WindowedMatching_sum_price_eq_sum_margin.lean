-- Prove2me | solution 1 for WindowedMatching.sum_price_eq_sum_margin
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:20:47.218241+00:00
-- url     : https://prove2.me/submissions/e2e7540c-ed13-4605-a56e-a0819a56a001

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WindowedMatching_sum_price_eq_sum_margin

open WindowedMatching

variable {n : ℕ}

theorem crit_p (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).p = st.p := by
  unfold critical
  split
  · rfl
  · dsimp only
    split_ifs <;> rfl

theorem crit_q (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).q = st.q := by
  unfold critical
  split
  · rfl
  · dsimp only
    split_ifs <;> rfl

theorem crit_S (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).S ⊆ st.S := by
  unfold critical
  split
  · exact Finset.Subset.refl _
  · dsimp only
    split_ifs
    · exact Finset.erase_subset _ _
    · exact Finset.erase_subset _ _

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

theorem bid_p_pos (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n)
    (h : 0 < margins d v k st (tie k st.S (margins d v k st))) :
    (bid d v tie k st).p = Function.update st.p (tie k st.S (margins d v k st))
      (onlineWeight d v (tie k st.S (margins d v k st)) k) := by
  unfold bid
  dsimp only
  rw [if_pos h]

theorem bid_p_neg (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n)
    (h : ¬ 0 < margins d v k st (tie k st.S (margins d v k st))) :
    (bid d v tie k st).p = st.p := by
  unfold bid
  dsimp only
  rw [if_neg h]

def Inv (t : ℕ) (st : State n) : Prop :=
  (∑ k, st.p k = ∑ k, st.q k) ∧
    ∀ k : Fin n, t ≤ k.val → st.p k = 0 ∧ st.q k = 0 ∧ k ∉ st.S

theorem sum_upd (f : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    ∑ x, Function.update f i b x = ∑ x, f x - f i + b := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) f]
  ring

theorem arrive_inv (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (t : ℕ) (k : Fin n) (hk : k.val = t) (st : State n) (hI : Inv t st) :
    Inv (t + 1) (arrive d v tie k st) := by
  obtain ⟨hsum, hfut⟩ := hI
  have hk0 := hfut k (le_of_eq hk.symm)
  obtain ⟨st0, hst0⟩ : ∃ x, x = addVertex k st := ⟨_, rfl⟩
  have hS0 : st0.S = insert k st.S := by rw [hst0]; rfl
  have hq0 : st0.q = st.q := by rw [hst0]; rfl
  have hp0 : st0.p = st.p := by
    rw [hst0]
    funext j
    show Function.update st.p k 0 j = st.p j
    rcases eq_or_ne j k with hj | hj
    · rw [hj, Function.update_self, hk0.1]
    · rw [Function.update_of_ne hj]
  have harr : arrive d v tie k st = bid d v tie k st0 := by rw [hst0]; rfl
  rw [harr]
  have hkS : k ∈ st0.S := by rw [hS0]; exact Finset.mem_insert_self _ _
  obtain ⟨r, hr⟩ : ∃ r, r = margins d v k st0 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = tie k st0.S r := ⟨_, rfl⟩
  have hrk : r k = 0 := by
    rw [hr]
    simp [margins, hkS, hp0, hk0.1, onlineWeight, SimpleGraph.irrefl]
  obtain ⟨hsS, hmax⟩ := hTie k st0.S r ⟨k, hkS⟩
  rw [← hs] at hsS hmax
  have hrs0 : 0 ≤ r s := by
    have := hmax k hkS
    rw [hrk] at this
    exact this
  have hrs : r s = onlineWeight d v s k - st.p s := by
    rw [hr]
    simp [margins, hsS, hp0]
  -- s is k or an earlier vertex
  have hslt : s.val ≤ t := by
    rw [hS0] at hsS
    rcases Finset.mem_insert.mp hsS with h | h
    · rw [h, hk]
    · by_contra hc
      exact (hfut s (by omega)).2.2 h
  have hq : (bid d v tie k st0).q = Function.update st.q k (r s) := by
    rw [bid_q, ← hr, ← hs, hq0]
  refine ⟨?_, ?_⟩
  · rw [hq, sum_upd, hk0.2.1]
    by_cases hpos : 0 < r s
    · have hpos' : 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
        rw [← hr, ← hs]; exact hpos
      rw [bid_p_pos d v tie k st0 hpos', ← hr, ← hs, hp0, sum_upd, hsum]
      linarith
    · have hpos' : ¬ 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
        rw [← hr, ← hs]; exact hpos
      rw [bid_p_neg d v tie k st0 hpos', hp0, hsum]
      have : r s = 0 := le_antisymm (not_lt.mp hpos) hrs0
      rw [this]
      ring
  · intro j hj
    have hjk : j ≠ k := by
      intro h; rw [h] at hj; omega
    have hjs : j ≠ s := by
      intro h; rw [h] at hj; omega
    have hf := hfut j (by omega)
    refine ⟨?_, ?_, ?_⟩
    · by_cases hpos : 0 < r s
      · have hpos' : 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
          rw [← hr, ← hs]; exact hpos
        rw [bid_p_pos d v tie k st0 hpos', ← hr, ← hs, hp0, Function.update_of_ne hjs]
        exact hf.1
      · have hpos' : ¬ 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
          rw [← hr, ← hs]; exact hpos
        rw [bid_p_neg d v tie k st0 hpos', hp0]
        exact hf.1
    · rw [hq, Function.update_of_ne hjk]
      exact hf.2.1
    · rw [bid_S, hS0]
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hjk h
      · exact hf.2.2 h

theorem crit_inv (ω : Fin n → Bool) (k : Fin n) (t : ℕ) (st : State n) (h : Inv t st) :
    Inv t (critical ω k st) := by
  rw [Inv, crit_p, crit_q]
  exact ⟨h.1, fun j hj => ⟨(h.2 j hj).1, (h.2 j hj).2.1,
    fun hm => (h.2 j hj).2.2 (crit_S ω k st hm)⟩⟩

theorem period_inv (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) (t : ℕ) (st : State n) (hI : Inv t st) :
    Inv (t + 1) (period d v tie ω t st) := by
  obtain ⟨st1, hst1⟩ : ∃ x, x = (if h : t < n then arrive d v tie ⟨t, h⟩ st else st) :=
    ⟨_, rfl⟩
  have h1 : Inv (t + 1) st1 := by
    rw [hst1]
    by_cases h : t < n
    · rw [dif_pos h]
      exact arrive_inv d v tie hTie t ⟨t, h⟩ rfl st hI
    · rw [dif_neg h]
      exact ⟨hI.1, fun k hk => hI.2 k (by omega)⟩
  have hper : period d v tie ω t st
      = if h : d ≤ t ∧ t - d < n then critical ω ⟨t - d, h.2⟩ st1 else st1 := by
    rw [hst1]; rfl
  rw [hper]
  by_cases h2 : d ≤ t ∧ t - d < n
  · rw [dif_pos h2]
    exact crit_inv ω _ _ _ h1
  · rw [dif_neg h2]
    exact h1

theorem inv_all (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) : ∀ t, Inv t (stateAfter d v tie ω t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, fun k _ => ⟨?_, ?_, ?_⟩⟩
    · simp [stateAfter, State.init]
    · simp [stateAfter, State.init]
    · simp [stateAfter, State.init]
    · simp [stateAfter, State.init]
  | succ t ih =>
    show Inv (t + 1) (period d v tie ω t (stateAfter d v tie ω t))
    exact period_inv d v tie hTie ω t _ ih

end Aux_WindowedMatching_sum_price_eq_sum_margin

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    ∑ k, (finalState d v tie ω).p k = ∑ k, (finalState d v tie ω).q k :=
  (Aux_WindowedMatching_sum_price_eq_sum_margin.inv_all d v tie hTie ω (n + d)).1
