-- Prove2me | solution 1 for WindowedMatching.dual_feasible
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:37:23.570185+00:00
-- url     : https://prove2.me/submissions/b5bffd20-fa7d-4245-ab06-b8bf707e7bc4

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WindowedMatching_dual_feasible

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

theorem arrive_S (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (arrive d v tie k st).S = insert k st.S := by
  unfold arrive
  rw [bid_S]
  rfl

def Inv (t : ℕ) (st : State n) : Prop :=
  (∀ k, 0 ≤ st.p k) ∧ (∀ k, 0 ≤ st.q k) ∧
    ∀ k : Fin n, t ≤ k.val → st.p k = 0 ∧ st.q k = 0 ∧ k ∉ st.S

def Step (t : ℕ) (st st' : State n) : Prop :=
  Inv (t + 1) st' ∧ (∀ k, st.p k ≤ st'.p k) ∧ (∀ k : Fin n, k.val < t → st'.q k = st.q k)

theorem arrive_step (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (t : ℕ) (k : Fin n) (hk : k.val = t) (st : State n) (hI : Inv t st) :
    Step t st (arrive d v tie k st) := by
  obtain ⟨hpn, hqn, hfut⟩ := hI
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
  have hslt : s.val ≤ t := by
    rw [hS0] at hsS
    rcases Finset.mem_insert.mp hsS with h | h
    · rw [h, hk]
    · by_contra hc
      exact (hfut s (by omega)).2.2 h
  have hq : (bid d v tie k st0).q = Function.update st.q k (r s) := by
    rw [bid_q, ← hr, ← hs, hq0]
  have hpcase : (bid d v tie k st0).p = st.p ∨
      (0 < r s ∧ (bid d v tie k st0).p = Function.update st.p s (onlineWeight d v s k)) := by
    by_cases hpos : 0 < r s
    · have hpos' : 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
        rw [← hr, ← hs]; exact hpos
      right
      refine ⟨hpos, ?_⟩
      rw [bid_p_pos d v tie k st0 hpos', ← hr, ← hs, hp0]
    · have hpos' : ¬ 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
        rw [← hr, ← hs]; exact hpos
      left
      rw [bid_p_neg d v tie k st0 hpos', hp0]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases hpcase with h | ⟨hpos, h⟩
    · rw [h]; exact hpn j
    · rw [h]
      by_cases hjs : j = s
      · rw [hjs, Function.update_self]
        have := hpn s
        linarith
      · rw [Function.update_of_ne hjs]
        exact hpn j
  · intro j
    rw [hq]
    by_cases hjk : j = k
    · rw [hjk, Function.update_self]
      exact hrs0
    · rw [Function.update_of_ne hjk]
      exact hqn j
  · intro j hj
    have hjk : j ≠ k := by
      intro h; rw [h] at hj; omega
    have hjs : j ≠ s := by
      intro h; rw [h] at hj; omega
    have hf := hfut j (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rcases hpcase with h | ⟨_, h⟩
      · rw [h]; exact hf.1
      · rw [h, Function.update_of_ne hjs]; exact hf.1
    · rw [hq, Function.update_of_ne hjk]
      exact hf.2.1
    · rw [bid_S, hS0]
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hjk h
      · exact hf.2.2 h
  · intro j
    rcases hpcase with h | ⟨hpos, h⟩
    · exact le_of_eq (congrFun h j).symm
    · by_cases hjs : j = s
      · rw [h, hjs, Function.update_self]
        linarith
      · exact le_of_eq (by rw [h, Function.update_of_ne hjs])
  · intro j hj
    have hjk : j ≠ k := by
      intro h; rw [h] at hj; omega
    rw [hq, Function.update_of_ne hjk]

theorem step_crit (ω : Fin n → Bool) (k : Fin n) (t : ℕ) (st st1 : State n)
    (h : Step t st st1) : Step t st (critical ω k st1) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [crit_p]; exact h1
  · rw [crit_q]; exact h2
  · intro j hj
    rw [crit_p, crit_q]
    exact ⟨(h3 j hj).1, (h3 j hj).2.1, fun hm => (h3 j hj).2.2 (crit_S ω k st1 hm)⟩
  · rw [crit_p]; exact h4
  · rw [crit_q]; exact h5

theorem period_step (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) (t : ℕ) (st : State n) (hI : Inv t st) :
    Step t st (period d v tie ω t st) := by
  obtain ⟨st1, hst1⟩ : ∃ x, x = (if h : t < n then arrive d v tie ⟨t, h⟩ st else st) :=
    ⟨_, rfl⟩
  have h1 : Step t st st1 := by
    rw [hst1]
    by_cases h : t < n
    · rw [dif_pos h]
      exact arrive_step d v tie hTie t ⟨t, h⟩ rfl st hI
    · rw [dif_neg h]
      exact ⟨⟨hI.1, hI.2.1, fun k hk => hI.2.2 k (by omega)⟩, fun _ => le_rfl, fun _ _ => rfl⟩
  have hper : period d v tie ω t st
      = if h : d ≤ t ∧ t - d < n then critical ω ⟨t - d, h.2⟩ st1 else st1 := by
    subst hst1; rfl
  rw [hper]
  by_cases h2 : d ≤ t ∧ t - d < n
  · rw [dif_pos h2]
    exact step_crit ω _ _ _ _ h1
  · rw [dif_neg h2]
    exact h1

theorem inv_all (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) : ∀ t, Inv t (stateAfter d v tie ω t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, ?_, fun k _ => ⟨?_, ?_, ?_⟩⟩
    · intro k; simp [stateAfter, State.init]
    · intro k; simp [stateAfter, State.init]
    · simp [stateAfter, State.init]
    · simp [stateAfter, State.init]
    · simp [stateAfter, State.init]
  | succ t ih =>
    show Inv (t + 1) (period d v tie ω t (stateAfter d v tie ω t))
    exact (period_step d v tie hTie ω t _ ih).1

theorem step_all (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) (t : ℕ) :
    Step t (stateAfter d v tie ω t) (stateAfter d v tie ω (t + 1)) :=
  period_step d v tie hTie ω t _ (inv_all d v tie hTie ω t)

theorem p_mono (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) (t : ℕ) (k : Fin n) :
    ∀ m, (stateAfter d v tie ω t).p k ≤ (stateAfter d v tie ω (t + m)).p k := by
  intro m
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact le_trans ih ((step_all d v tie hTie ω (t + m)).2.1 k)

theorem q_stable (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (hTie : IsArgmaxRule tie)
    (ω : Fin n → Bool) (k : Fin n) :
    ∀ m, (stateAfter d v tie ω (k.val + 1 + m)).q k = (stateAfter d v tie ω (k.val + 1)).q k := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih]
    exact (step_all d v tie hTie ω (k.val + 1 + m)).2.2 k (by omega)

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

theorem margin_ge (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (i j : Fin n) (hij : i < j)
    (hj : (j : ℕ) ≤ i + d) :
    v s(i, j) - (stateAfter d v tie ω j).p i ≤ (stateAfter d v tie ω (j + 1)).q j := by
  have hij' : (i : ℕ) < j := hij
  have hS := S_inv d hd v tie ω j i hij' hj
  obtain ⟨st, hst⟩ : ∃ x, x = stateAfter d v tie ω j := ⟨_, rfl⟩
  rw [← hst] at hS ⊢
  have hstep : stateAfter d v tie ω (j + 1) = period d v tie ω j st := by
    subst hst; rfl
  have hq : (period d v tie ω j st).q = (arrive d v tie j st).q := by
    unfold period
    dsimp only
    rw [dif_pos j.isLt]
    by_cases h2 : d ≤ (j : ℕ) ∧ (j : ℕ) - d < n
    · rw [dif_pos h2, crit_q]
      all_goals rfl
    · rw [dif_neg h2]
      all_goals rfl
  rw [hstep, hq]
  unfold arrive
  rw [bid_q, Function.update_self]
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

theorem edge_bound (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (i j : Fin n) (hij : i < j)
    (hj : (j : ℕ) ≤ i + d) :
    v s(i, j) ≤ (finalState d v tie ω).p i + (finalState d v tie ω).q j := by
  have h1 := margin_ge d hd v tie hTie ω i j hij hj
  have h2 := p_mono d v tie hTie ω (j : ℕ) i (n + d - j)
  have h3 := q_stable d v tie hTie ω j (n + d - (j + 1))
  have hjn := j.isLt
  rw [show (j : ℕ) + (n + d - j) = n + d by omega] at h2
  rw [show (j : ℕ) + 1 + (n + d - (j + 1)) = n + d by omega] at h3
  unfold finalState
  linarith

end Aux_WindowedMatching_dual_feasible

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    (∀ k, 0 ≤ (finalState d v tie ω).p k + (finalState d v tie ω).q k) ∧
    (∀ k l, (windowGraph n d).Adj k l →
      v s(k, l) ≤ ((finalState d v tie ω).p k + (finalState d v tie ω).q k) +
        ((finalState d v tie ω).p l + (finalState d v tie ω).q l)) := by
  have hI := Aux_WindowedMatching_dual_feasible.inv_all d v tie hTie ω (n + d)
  have hp : ∀ k, 0 ≤ (finalState d v tie ω).p k := hI.1
  have hq : ∀ k, 0 ≤ (finalState d v tie ω).q k := hI.2.1
  refine ⟨fun k => add_nonneg (hp k) (hq k), ?_⟩
  intro k l hkl
  obtain ⟨hne, habs⟩ := hkl
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (k : ℕ) < l := h
    have hb := Aux_WindowedMatching_dual_feasible.edge_bound d hd v tie hTie ω k l h
      (by rw [abs_le] at habs; omega)
    have := hp l
    have := hq k
    linarith
  · have h' : (l : ℕ) < k := h
    have hb := Aux_WindowedMatching_dual_feasible.edge_bound d hd v tie hTie ω l k h
      (by rw [abs_le] at habs; omega)
    rw [Sym2.eq_swap] at hb
    have := hp k
    have := hq l
    linarith
