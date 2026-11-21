-- Prove2me | solution 1 for WindowedMatching.disjoint_paths
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:41:55.477217+00:00
-- url     : https://prove2.me/submissions/1c256c81-f175-4752-a2a0-9cf5357bebc9

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WindowedMatching_disjoint_paths

open WindowedMatching

variable {n : ℕ}

theorem crit_p (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).p = st.p := by
  unfold critical
  split
  · rfl
  · dsimp only
    split_ifs <;> rfl

theorem crit_m (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).m = st.m := by
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

theorem bid_m_pos (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n)
    (h : 0 < margins d v k st (tie k st.S (margins d v k st))) :
    (bid d v tie k st).m = Function.update st.m (tie k st.S (margins d v k st)) (some k) := by
  unfold bid
  dsimp only
  rw [if_pos h]

theorem bid_m_neg (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n)
    (h : ¬ 0 < margins d v k st (tie k st.S (margins d v k st))) :
    (bid d v tie k st).m = st.m := by
  unfold bid
  dsimp only
  rw [if_neg h]

theorem ow_nonneg (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (a b : Fin n) :
    0 ≤ onlineWeight d v a b := by
  unfold onlineWeight
  split_ifs
  · exact hv _
  · exact le_rfl

def J (d : ℕ) (t : ℕ) (st : State n) : Prop :=
  (∀ k, 0 ≤ st.p k) ∧ (∀ x, x ∈ st.S → x.val < t) ∧
  (∀ k l, st.m k = some l → k < l ∧ (windowGraph n d).Adj k l ∧ l.val < t) ∧
  (∀ k k' l, st.m k = some l → st.m k' = some l → k = k')

theorem arrive_J (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (tie : TieRule n)
    (hTie : IsArgmaxRule tie) (t : ℕ) (k : Fin n) (hk : k.val = t) (st : State n)
    (hJ : J d t st) : J d (t + 1) (arrive d v tie k st) := by
  obtain ⟨hpn, hSlt, hmA, hmI⟩ := hJ
  obtain ⟨st0, hst0⟩ : ∃ x, x = addVertex k st := ⟨_, rfl⟩
  have hS0 : st0.S = insert k st.S := by rw [hst0]; rfl
  have hp0 : st0.p = Function.update st.p k 0 := by rw [hst0]; rfl
  have hm0 : st0.m = Function.update st.m k none := by rw [hst0]; rfl
  have harr : arrive d v tie k st = bid d v tie k st0 := by rw [hst0]; rfl
  rw [harr]
  have hp0n : ∀ x, 0 ≤ st0.p x := by
    intro x
    rw [hp0]
    by_cases hx : x = k
    · exact le_of_eq (by rw [hx, Function.update_self])
    · rw [Function.update_of_ne hx]; exact hpn x
  have hm0k : st0.m k = none := by rw [hm0, Function.update_self]
  have hold : ∀ z l, st0.m z = some l → z ≠ k ∧ st.m z = some l := by
    intro z l hz
    have hzk : z ≠ k := by
      intro h
      rw [h, hm0k] at hz
      simp at hz
    refine ⟨hzk, ?_⟩
    rw [hm0, Function.update_of_ne hzk] at hz
    exact hz
  have hkS : k ∈ st0.S := by rw [hS0]; exact Finset.mem_insert_self _ _
  obtain ⟨r, hr⟩ : ∃ r, r = margins d v k st0 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = tie k st0.S r := ⟨_, rfl⟩
  have hsS : s ∈ st0.S := by
    rw [hs]
    exact (hTie k st0.S r ⟨k, hkS⟩).1
  have hrs : r s = onlineWeight d v s k - st0.p s := by
    rw [hr]
    simp [margins, hsS]
  have hcase : ((bid d v tie k st0).p = st0.p ∧ (bid d v tie k st0).m = st0.m) ∨
      (0 < r s ∧ (bid d v tie k st0).p = Function.update st0.p s (onlineWeight d v s k) ∧
        (bid d v tie k st0).m = Function.update st0.m s (some k)) := by
    by_cases hpos : 0 < r s
    · have hpos' : 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
        rw [← hr, ← hs]; exact hpos
      right
      refine ⟨hpos, ?_, ?_⟩
      · rw [bid_p_pos d v tie k st0 hpos', ← hr, ← hs]
      · rw [bid_m_pos d v tie k st0 hpos', ← hr, ← hs]
    · have hpos' : ¬ 0 < margins d v k st0 (tie k st0.S (margins d v k st0)) := by
        rw [← hr, ← hs]; exact hpos
      left
      exact ⟨bid_p_neg d v tie k st0 hpos', bid_m_neg d v tie k st0 hpos'⟩
  -- consequences of a positive bid
  have hposfacts : 0 < r s → (windowGraph n d).Adj s k ∧ s.val < t := by
    intro hpos
    have hown : 0 < onlineWeight d v s k := by
      have := hp0n s
      linarith
    have hadj : (windowGraph n d).Adj s k := by
      by_contra hna
      unfold onlineWeight at hown
      rw [if_neg hna] at hown
      exact lt_irrefl _ hown
    refine ⟨hadj, ?_⟩
    have hsk : s ≠ k := hadj.1
    have hsS' := hsS
    rw [hS0] at hsS'
    rcases Finset.mem_insert.mp hsS' with h | h
    · exact absurd h hsk
    · exact hSlt s h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rcases hcase with ⟨hp, _⟩ | ⟨_, hp, _⟩
    · rw [hp]; exact hp0n x
    · rw [hp]
      by_cases hxs : x = s
      · rw [hxs, Function.update_self]
        exact ow_nonneg d v hv s k
      · rw [Function.update_of_ne hxs]
        exact hp0n x
  · rw [bid_S, hS0]
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; omega
    · have := hSlt x h
      omega
  · intro x l hx
    rcases hcase with ⟨_, hm⟩ | ⟨hpos, _, hm⟩
    · rw [hm] at hx
      obtain ⟨_, hx'⟩ := hold x l hx
      obtain ⟨a, b, c⟩ := hmA x l hx'
      exact ⟨a, b, by omega⟩
    · rw [hm] at hx
      by_cases hxs : x = s
      · rw [hxs, Function.update_self] at hx
        have hlk : k = l := Option.some.inj hx
        rw [← hlk, hxs]
        obtain ⟨hadj, hslt⟩ := hposfacts hpos
        refine ⟨?_, hadj, by omega⟩
        show s.val < k.val
        omega
      · rw [Function.update_of_ne hxs] at hx
        obtain ⟨_, hx'⟩ := hold x l hx
        obtain ⟨a, b, c⟩ := hmA x l hx'
        exact ⟨a, b, by omega⟩
  · intro x y l hx hy
    rcases hcase with ⟨_, hm⟩ | ⟨_, _, hm⟩
    · rw [hm] at hx hy
      exact hmI x y l (hold x l hx).2 (hold y l hy).2
    · rw [hm] at hx hy
      by_cases hxs : x = s
      · by_cases hys : y = s
        · rw [hxs, hys]
        · exfalso
          rw [hxs, Function.update_self] at hx
          rw [Function.update_of_ne hys] at hy
          have hlk : k = l := Option.some.inj hx
          rw [← hlk] at hy
          have := (hmA y k (hold y k hy).2).2.2
          omega
      · by_cases hys : y = s
        · exfalso
          rw [hys, Function.update_self] at hy
          rw [Function.update_of_ne hxs] at hx
          have hlk : k = l := Option.some.inj hy
          rw [← hlk] at hx
          have := (hmA x k (hold x k hx).2).2.2
          omega
        · rw [Function.update_of_ne hxs] at hx
          rw [Function.update_of_ne hys] at hy
          exact hmI x y l (hold x l hx).2 (hold y l hy).2

theorem crit_J (d : ℕ) (ω : Fin n → Bool) (k : Fin n) (t : ℕ) (st : State n) (h : J d t st) :
    J d t (critical ω k st) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [crit_p]; exact h1
  · intro x hx; exact h2 x (crit_S ω k st hx)
  · rw [crit_m]; exact h3
  · rw [crit_m]; exact h4

theorem period_J (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (tie : TieRule n)
    (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (t : ℕ) (st : State n) (hI : J d t st) :
    J d (t + 1) (period d v tie ω t st) := by
  obtain ⟨st1, hst1⟩ : ∃ x, x = (if h : t < n then arrive d v tie ⟨t, h⟩ st else st) :=
    ⟨_, rfl⟩
  have h1 : J d (t + 1) st1 := by
    rw [hst1]
    by_cases h : t < n
    · rw [dif_pos h]
      exact arrive_J d v hv tie hTie t ⟨t, h⟩ rfl st hI
    · rw [dif_neg h]
      obtain ⟨a, b, c, e⟩ := hI
      refine ⟨a, fun x hx => by have := b x hx; omega, fun k l hkl => ?_, e⟩
      obtain ⟨c1, c2, c3⟩ := c k l hkl
      exact ⟨c1, c2, by omega⟩
  have hper : period d v tie ω t st
      = if h : d ≤ t ∧ t - d < n then critical ω ⟨t - d, h.2⟩ st1 else st1 := by
    subst hst1; rfl
  rw [hper]
  by_cases h2 : d ≤ t ∧ t - d < n
  · rw [dif_pos h2]
    exact crit_J d ω _ _ _ h1
  · rw [dif_neg h2]
    exact h1

theorem J_all (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (tie : TieRule n)
    (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) : ∀ t, J d t (stateAfter d v tie ω t) := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k; simp [stateAfter, State.init]
    · intro x hx; simp [stateAfter, State.init] at hx
    · intro k l hkl; simp [stateAfter, State.init] at hkl
    · intro k k' l hkl; simp [stateAfter, State.init] at hkl
  | succ t ih =>
    show J d (t + 1) (period d v tie ω t (stateAfter d v tie ω t))
    exact period_J d v hv tie hTie ω t _ ih

end Aux_WindowedMatching_disjoint_paths

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    (∀ k l, (finalState d v tie ω).m k = some l → k < l ∧ (windowGraph n d).Adj k l) ∧
    (∀ k k' l, (finalState d v tie ω).m k = some l → (finalState d v tie ω).m k' = some l →
      k = k') := by
  obtain ⟨_, _, h3, h4⟩ := Aux_WindowedMatching_disjoint_paths.J_all d v hv tie hTie ω (n + d)
  exact ⟨fun k l h => ⟨(h3 k l h).1, (h3 k l h).2.1⟩, h4⟩
