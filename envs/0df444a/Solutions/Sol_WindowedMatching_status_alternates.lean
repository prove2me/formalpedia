-- Prove2me | solution 1 for WindowedMatching.status_alternates
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:50:17.318908+00:00
-- url     : https://prove2.me/submissions/dcd44e9c-abda-4a85-a17f-40f1cfa66670

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace Aux_WM_S3

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

theorem crit_none (ω : Fin n → Bool) (k : Fin n) (st : State n) (h : st.m k = none) :
    critical ω k st = st := by
  simp [critical, h]

theorem crit_S_some (ω : Fin n → Bool) (k : Fin n) (st : State n) (l : Fin n)
    (h : st.m k = some l) : (critical ω k st).S = st.S.erase k := by
  rcases hs : st.status k with _ | _ | _ <;> cases hω : ω k <;> simp [critical, h, hs, hω]

theorem crit_some (ω : Fin n → Bool) (k : Fin n) (st : State n) (l : Fin n)
    (h : st.m k = some l) :
    ∃ b : Bool,
      (critical ω k st).status = Function.update (Function.update st.status k
        (if b then Status.seller else Status.buyer)) l (if b then Status.buyer else Status.seller) ∧
      (critical ω k st).finalized = (if b then st.finalized ++ [(k, l)] else st.finalized) ∧
      (st.status k = Status.seller → b = true) ∧ (st.status k = Status.buyer → b = false) ∧
      (st.status k = Status.undetermined → b = ω k) := by
  rcases hs : st.status k with _ | _ | _
  · refine ⟨ω k, ?_, ?_, ?_, ?_, ?_⟩
    · cases hω : ω k <;> simp [critical, h, hs, hω]
    · cases hω : ω k <;> simp [critical, h, hs, hω]
    · intro h'; exact absurd h' (by simp)
    · intro h'; exact absurd h' (by simp)
    · intro _; rfl
  · refine ⟨true, ?_, ?_, ?_, ?_, ?_⟩
    · simp [critical, h, hs]
    · simp [critical, h, hs]
    · intro _; rfl
    · intro h'; exact absurd h' (by simp)
    · intro h'; exact absurd h' (by simp)
  · refine ⟨false, ?_, ?_, ?_, ?_, ?_⟩
    · simp [critical, h, hs]
    · simp [critical, h, hs]
    · intro h'; exact absurd h' (by simp)
    · intro _; rfl
    · intro h'; exact absurd h' (by simp)

theorem bid_S (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (bid d v tie k st).S = st.S := by
  unfold bid
  dsimp only
  split_ifs <;> rfl

theorem bid_status (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (bid d v tie k st).status = st.status := by
  unfold bid
  dsimp only
  split_ifs <;> rfl

theorem bid_fin (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n) (st : State n) :
    (bid d v tie k st).finalized = st.finalized := by
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

structure Inv (d : ℕ) (v : Sym2 (Fin n) → ℝ) (ω : Fin n → Bool) (a c : ℕ) (st : State n) :
    Prop where
  hS : ∀ x ∈ st.S, x.val < a
  hm : ∀ x y, st.m x = some y → x.val < y.val ∧ y.val < a
  hp0 : ∀ x, st.m x = none → st.p x = 0
  hp1 : ∀ x y, st.m x = some y → st.p x = v s(x, y)
  hu : ∀ x x' y, st.m x = some y → st.m x' = some y → x = x'
  hJ : ∀ x y, x.val + d < c → st.m x = some y →
    (st.status x = Status.seller ∧ st.status y = Status.buyer ∧ (x, y) ∈ st.finalized) ∨
    (st.status x = Status.buyer ∧ st.status y = Status.seller ∧ (x, y) ∉ st.finalized)
  hK : ∀ x, c ≤ x.val + d → (∀ j, j.val + d < c → st.m j ≠ some x) →
    st.status x = Status.undetermined
  hL : ∀ x y, x.val + d < c → st.m x = some y → (∀ j, j.val + d < c → st.m j ≠ some x) →
    (st.status x = Status.seller ↔ ω x = true)
  hE : ∀ e ∈ st.finalized, e.1.val + d < c
  hR : (st.finalized.map fun e => v s(e.1, e.2)).sum =
    ∑ x, if x.val + d < c ∧ st.status x = Status.seller then st.p x else 0

theorem Inv.pnn {d : ℕ} {v : Sym2 (Fin n) → ℝ} {ω : Fin n → Bool} {a c : ℕ} {st : State n}
    (hv : ∀ e, 0 ≤ v e) (h : Inv d v ω a c st) (x : Fin n) : 0 ≤ st.p x := by
  rcases hx : st.m x with _ | y
  · exact le_of_eq (h.hp0 x hx).symm
  · rw [h.hp1 x y hx]; exact hv _

theorem inv_init (d : ℕ) (v : Sym2 (Fin n) → ℝ) (ω : Fin n → Bool) :
    Inv d v ω 0 0 (State.init n) where
  hS := by intro x hx; simp [State.init] at hx
  hm := by intro x y h; simp [State.init] at h
  hp0 := by intro x _; rfl
  hp1 := by intro x y h; simp [State.init] at h
  hu := by intro x x' y h; simp [State.init] at h
  hJ := by intro x y h; exact absurd h (by omega)
  hK := by intro x _ _; rfl
  hL := by intro x y h; exact absurd h (by omega)
  hE := by intro e he; simp [State.init] at he
  hR := by simp [State.init]

theorem inv_mono {d : ℕ} {v : Sym2 (Fin n) → ℝ} {ω : Fin n → Bool} {a a' c : ℕ} {st : State n}
    (h : Inv d v ω a c st) (ha : a ≤ a') : Inv d v ω a' c st :=
  { h with
    hS := fun x hx => lt_of_lt_of_le (h.hS x hx) ha
    hm := fun x y hxy => ⟨(h.hm x y hxy).1, lt_of_lt_of_le (h.hm x y hxy).2 ha⟩ }

theorem inv_arrive (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (tie : TieRule n)
    (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (t : ℕ) (k : Fin n) (hk : k.val = t)
    (st : State n) (hI : Inv d v ω t t st) : Inv d v ω (t + 1) t (arrive d v tie k st) := by
  obtain ⟨st0, hst0⟩ : ∃ x, x = addVertex k st := ⟨_, rfl⟩
  have eS0 : st0.S = insert k st.S := by rw [hst0]; rfl
  have eP0 : st0.p = Function.update st.p k 0 := by rw [hst0]; rfl
  have eM0 : st0.m = Function.update st.m k none := by rw [hst0]; rfl
  have eT0 : st0.status = Function.update st.status k Status.undetermined := by rw [hst0]; rfl
  have eF0 : st0.finalized = st.finalized := by rw [hst0]; rfl
  have harr : arrive d v tie k st = bid d v tie k st0 := by rw [hst0]; rfl
  rw [harr]
  have hp0n : ∀ x, 0 ≤ st0.p x := by
    intro x
    rw [eP0]
    by_cases hx : x = k
    · exact le_of_eq (by rw [hx, Function.update_self])
    · rw [Function.update_of_ne hx]; exact Inv.pnn hv hI x
  have hpold : ∀ z, z ≠ k → st0.p z = st.p z := by
    intro z hz; rw [eP0, Function.update_of_ne hz]
  have hm0k : st0.m k = none := by rw [eM0, Function.update_self]
  have hold : ∀ z l, st0.m z = some l → z ≠ k ∧ st.m z = some l := by
    intro z l hz
    have hzk : z ≠ k := by
      intro h
      rw [h, hm0k] at hz
      simp at hz
    refine ⟨hzk, ?_⟩
    rw [eM0, Function.update_of_ne hzk] at hz
    exact hz
  have hkS : k ∈ st0.S := by rw [eS0]; exact Finset.mem_insert_self _ _
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
  have hposfacts : 0 < r s → (windowGraph n d).Adj s k ∧ s.val < t ∧ t ≤ s.val + d ∧
      onlineWeight d v s k = v s(s, k) := by
    intro hpos
    have hown : 0 < onlineWeight d v s k := by
      have := hp0n s
      linarith
    have hadj : (windowGraph n d).Adj s k := by
      by_contra hna
      unfold onlineWeight at hown
      rw [if_neg hna] at hown
      exact lt_irrefl _ hown
    have hsk : s ≠ k := hadj.1
    have hslt : s.val < t := by
      have hsS' := hsS
      rw [eS0] at hsS'
      rcases Finset.mem_insert.mp hsS' with h | h
      · exact absurd h hsk
      · exact hI.hS s h
    have hge : t ≤ s.val + d := by
      have h2 := hadj.2
      rw [abs_le] at h2
      omega
    have how : onlineWeight d v s k = v s(s, k) := by
      unfold onlineWeight
      rw [if_pos hadj]
    exact ⟨hadj, hslt, hge, how⟩
  have hstat : ∀ z, z ≠ k → (bid d v tie k st0).status z = st.status z := by
    intro z hz; rw [bid_status, eT0, Function.update_of_ne hz]
  have hBf : (bid d v tie k st0).finalized = st.finalized := by rw [bid_fin, eF0]
  have frozen : ∀ x : Fin n, x.val + d < t →
      (bid d v tie k st0).m x = st.m x ∧ (bid d v tie k st0).p x = st.p x := by
    intro x hx
    have hxk : x ≠ k := by intro h; rw [h] at hx; omega
    rcases hcase with ⟨hp, hm⟩ | ⟨hpos, hp, hm⟩
    · rw [hp, hm, eM0, hpold x hxk, Function.update_of_ne hxk]; exact ⟨rfl, rfl⟩
    · have hxs : x ≠ s := by
        intro h
        have := (hposfacts hpos).2.2.1
        rw [h] at hx
        omega
      rw [hp, hm, Function.update_of_ne hxs, Function.update_of_ne hxs, eM0, hpold x hxk,
        Function.update_of_ne hxk]
      exact ⟨rfl, rfl⟩
  have mspec : ∀ x y, (bid d v tie k st0).m x = some y →
      (st.m x = some y ∧ x ≠ k ∧ (bid d v tie k st0).p x = st.p x) ∨
      (y = k ∧ x = s ∧ x.val < t ∧ (bid d v tie k st0).p x = v s(x, k)) := by
    intro x y hxy
    rcases hcase with ⟨hp, hm⟩ | ⟨hpos, hp, hm⟩
    · rw [hm] at hxy
      obtain ⟨hxk, hx⟩ := hold x y hxy
      left
      exact ⟨hx, hxk, by rw [hp, hpold x hxk]⟩
    · rw [hm] at hxy
      obtain ⟨_, hslt, _, how⟩ := hposfacts hpos
      by_cases hxs : x = s
      · rw [hxs, Function.update_self] at hxy
        right
        refine ⟨(Option.some.inj hxy).symm, hxs, by rw [hxs]; exact hslt, ?_⟩
        rw [hp, hxs, Function.update_self, how]
      · rw [Function.update_of_ne hxs] at hxy
        obtain ⟨hxk, hx⟩ := hold x y hxy
        left
        exact ⟨hx, hxk, by rw [hp, Function.update_of_ne hxs, hpold x hxk]⟩
  have hpn0 : ∀ x, (bid d v tie k st0).m x = none → (bid d v tie k st0).p x = 0 := by
    intro x hx
    by_cases hxk : x = k
    · rcases hcase with ⟨hp, _⟩ | ⟨hpos, hp, _⟩
      · rw [hp, hxk, eP0, Function.update_self]
      · rw [hp, hxk, Function.update_of_ne (hposfacts hpos).1.1.symm, eP0,
          Function.update_self]
    · have hm' : st.m x = none := by
        rcases hcase with ⟨_, hm⟩ | ⟨hpos, _, hm⟩
        · rw [hm, eM0, Function.update_of_ne hxk] at hx; exact hx
        · by_cases hxs : x = s
          · rw [hm, hxs, Function.update_self] at hx; exact absurd hx (by simp)
          · rw [hm, Function.update_of_ne hxs, eM0, Function.update_of_ne hxk] at hx; exact hx
      rcases hcase with ⟨hp, _⟩ | ⟨hpos, hp, hm⟩
      · rw [hp, hpold x hxk]; exact hI.hp0 x hm'
      · have hxs : x ≠ s := by
          intro h
          rw [hm, h, Function.update_self] at hx
          exact absurd hx (by simp)
        rw [hp, Function.update_of_ne hxs, hpold x hxk]; exact hI.hp0 x hm'
  refine ⟨?_, ?_, hpn0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bid_S, eS0]
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; omega
    · have := hI.hS x h
      omega
  · intro x y hxy
    rcases mspec x y hxy with ⟨h1, _, _⟩ | ⟨h1, _, h3, _⟩
    · have := hI.hm x y h1
      exact ⟨this.1, by omega⟩
    · rw [h1]
      exact ⟨by omega, by omega⟩
  · intro x y hxy
    rcases mspec x y hxy with ⟨h1, _, h3⟩ | ⟨h1, _, _, h4⟩
    · rw [h3]; exact hI.hp1 x y h1
    · rw [h4, h1]
  · intro x x' y hx hx'
    rcases mspec x y hx with ⟨h1, _, _⟩ | ⟨h1, h2, _, _⟩ <;>
      rcases mspec x' y hx' with ⟨h1', _, _⟩ | ⟨h1', h2', _, _⟩
    · exact hI.hu x x' y h1 h1'
    · exfalso
      rw [h1'] at h1
      have := (hI.hm x k h1).2
      omega
    · exfalso
      rw [h1] at h1'
      have := (hI.hm x' k h1').2
      omega
    · rw [h2, h2']
  · intro x y hx hxy
    obtain ⟨hfm, _⟩ := frozen x hx
    rw [hfm] at hxy
    have hxk : x ≠ k := by intro h; rw [h] at hx; omega
    have hyk : y ≠ k := by
      intro h
      rw [h] at hxy
      have := (hI.hm x k hxy).2
      omega
    rw [hstat x hxk, hstat y hyk, hBf]
    exact hI.hJ x y hx hxy
  · intro x hx H
    by_cases hxk : x = k
    · rw [hxk, bid_status, eT0, Function.update_self]
    · rw [hstat x hxk]
      exact hI.hK x hx (fun j hj => by rw [← (frozen j hj).1]; exact H j hj)
  · intro x y hx hxy H
    have hxk : x ≠ k := by intro h; rw [h] at hx; omega
    rw [hstat x hxk]
    exact hI.hL x y hx (by rw [← (frozen x hx).1]; exact hxy)
      (fun j hj => by rw [← (frozen j hj).1]; exact H j hj)
  · rw [hBf]; exact hI.hE
  · rw [hBf, hI.hR]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x.val + d < t
    · have hxk : x ≠ k := by intro h; rw [h] at hx; omega
      rw [hstat x hxk, (frozen x hx).2]
    · simp [hx]

theorem inv_crit (d : ℕ) (v : Sym2 (Fin n) → ℝ) (ω : Fin n → Bool) (t : ℕ) (c : Fin n)
    (hc : c.val + d = t) (st : State n) (hI : Inv d v ω (t + 1) t st) :
    Inv d v ω (t + 1) (t + 1) (critical ω c st) := by
  have hlt : ∀ x : Fin n, x.val + d < t + 1 → x.val + d < t ∨ x = c := by
    intro x hx
    by_cases h : x.val + d < t
    · exact Or.inl h
    · exact Or.inr (Fin.ext (by omega))
  rcases hmc : st.m c with _ | l
  · rw [crit_none ω c st hmc]
    refine ⟨hI.hS, hI.hm, hI.hp0, hI.hp1, hI.hu, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y hx hxy
      rcases hlt x hx with h | h
      · exact hI.hJ x y h hxy
      · rw [h, hmc] at hxy; exact absurd hxy (by simp)
    · intro x hx H
      exact hI.hK x (by omega) (fun j hj => H j (by omega))
    · intro x y hx hxy H
      rcases hlt x hx with h | h
      · exact hI.hL x y h hxy (fun j hj => H j (by omega))
      · rw [h, hmc] at hxy; exact absurd hxy (by simp)
    · intro e he; have := hI.hE e he; omega
    · rw [hI.hR]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxc : x = c
      · rw [hxc, hI.hp0 c hmc]; simp
      · by_cases h1 : x.val + d < t
        · have h2 : x.val + d < t + 1 := by omega
          simp [h1, h2]
        · have h2 : ¬ x.val + d < t + 1 := fun h => h1 ((hlt x h).resolve_right hxc)
          simp [h1, h2]
  · obtain ⟨b, hst, hfin, hb1, hb2, hb3⟩ := crit_some ω c st l hmc
    have hcl : c.val < l.val := (hI.hm c l hmc).1
    have hlc : l ≠ c := by intro h; rw [h] at hcl; exact lt_irrefl _ hcl
    have hsz : ∀ z, z ≠ c → z ≠ l → (critical ω c st).status z = st.status z := by
      intro z h1 h2; rw [hst, Function.update_of_ne h2, Function.update_of_ne h1]
    have hsc : (critical ω c st).status c = (if b then Status.seller else Status.buyer) := by
      rw [hst, Function.update_of_ne hlc.symm, Function.update_self]
    have hsl : (critical ω c st).status l = (if b then Status.buyer else Status.seller) := by
      rw [hst, Function.update_self]
    have hpred : ∀ j : Fin n, j.val + d < t → st.m j = some c →
        (critical ω c st).status c = st.status c := by
      intro j hj hjc
      rw [hsc]
      rcases hI.hJ j c hj hjc with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
      · simp [h2, hb2 h2]
      · simp [h2, hb1 h2]
    have hmemiff : ∀ a b', a ≠ c →
        ((a, b') ∈ (critical ω c st).finalized ↔ (a, b') ∈ st.finalized) := by
      intro a b' ha; rw [hfin]; cases b <;> simp [ha]
    have hnotin : (c, l) ∉ st.finalized := by
      intro hmem
      have := hI.hE (c, l) hmem
      exact absurd this (by show ¬ (c.val + d < t); omega)
    refine ⟨fun x hx => hI.hS x (crit_S ω c st hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [crit_m]; exact hI.hm
    · rw [crit_m, crit_p]; exact hI.hp0
    · rw [crit_m, crit_p]; exact hI.hp1
    · rw [crit_m]; exact hI.hu
    · intro x y hx hxy
      rw [crit_m] at hxy
      rcases hlt x hx with h | h
      · have hxc : x ≠ c := by intro e; rw [e] at h; omega
        have hxl : x ≠ l := by intro e; rw [e] at h; omega
        have hyl : y ≠ l := by
          intro e; rw [e] at hxy; exact hxc (hI.hu x c l hxy hmc)
        have hsy : (critical ω c st).status y = st.status y := by
          by_cases hyc : y = c
          · rw [hyc]; rw [hyc] at hxy; exact hpred x h hxy
          · exact hsz y hyc hyl
        rw [hsz x hxc hxl, hsy, hmemiff x y hxc]
        exact hI.hJ x y h hxy
      · rw [h] at hxy ⊢
        have hyl : y = l := by rw [hmc] at hxy; exact (Option.some.inj hxy).symm
        rw [hyl, hsc, hsl, hfin]
        cases b <;> simp [hnotin]
    · intro x hx H
      have hxc : x ≠ c := by intro e; rw [e] at hx; omega
      have hxl : x ≠ l := by
        intro e
        apply H c (by omega)
        rw [crit_m, hmc, e]
      rw [hsz x hxc hxl]
      exact hI.hK x (by omega) (fun j hj => by have := H j (by omega); rwa [crit_m] at this)
    · intro x y hx hxy H
      rw [crit_m] at hxy
      have H' : ∀ j : Fin n, j.val + d < t → st.m j ≠ some x := fun j hj => by
        have := H j (by omega); rwa [crit_m] at this
      rcases hlt x hx with h | h
      · have hxc : x ≠ c := by intro e; rw [e] at h; omega
        have hxl : x ≠ l := by intro e; rw [e] at h; omega
        rw [hsz x hxc hxl]
        exact hI.hL x y h hxy H'
      · rw [h] at H' ⊢
        have hund := hI.hK c (by omega) H'
        rw [hsc, hb3 hund]
        cases hω : ω c <;> simp
    · intro e he
      rw [hfin] at he
      have he' : e ∈ st.finalized ∨ e = (c, l) := by
        cases b
        · left; simpa using he
        · simpa using he
      rcases he' with he' | he'
      · have := hI.hE e he'; omega
      · rw [he']; show c.val + d < t + 1; omega
    · have key : ∀ x : Fin n,
          (if x.val + d < t + 1 ∧ (critical ω c st).status x = Status.seller
            then (critical ω c st).p x else 0) =
          (if x.val + d < t ∧ st.status x = Status.seller then st.p x else 0) +
            (if x = c then (if b then v s(c, l) else 0) else 0) := by
        intro x
        rw [crit_p]
        by_cases hxc : x = c
        · rw [hxc, hsc, hI.hp1 c l hmc]
          have h1 : ¬ (c.val + d < t) := by omega
          have h2 : c.val + d < t + 1 := by omega
          cases b <;> simp [h1, h2]
        · by_cases hxl : x = l
          · rw [hxl]
            have h1 : ¬ (l.val + d < t) := by omega
            have h2 : ¬ (l.val + d < t + 1) := by omega
            simp [h1, h2, hlc]
          · rw [hsz x hxc hxl]
            by_cases h1 : x.val + d < t
            · have h2 : x.val + d < t + 1 := by omega
              simp [h1, h2, hxc]
            · have h2 : ¬ (x.val + d < t + 1) := fun h => h1 ((hlt x h).resolve_right hxc)
              simp [h1, h2, hxc]
      rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib, ← hI.hR, hfin]
      cases b <;> simp

theorem inv_nocrit (d : ℕ) (v : Sym2 (Fin n) → ℝ) (ω : Fin n → Bool) (a t : ℕ)
    (hnc : ¬ (d ≤ t ∧ t - d < n)) (st : State n) (hI : Inv d v ω a t st) :
    Inv d v ω a (t + 1) st := by
  have hiff : ∀ x : Fin n, x.val + d < t + 1 → x.val + d < t := by
    intro x hx
    by_contra h'
    exact hnc ⟨by omega, by have := x.isLt; omega⟩
  refine ⟨hI.hS, hI.hm, hI.hp0, hI.hp1, hI.hu, fun x y hx hxy => hI.hJ x y (hiff x hx) hxy,
    fun x hx H => hI.hK x (by omega) (fun j hj => H j (by omega)),
    fun x y hx hxy H => hI.hL x y (hiff x hx) hxy (fun j hj => H j (by omega)),
    fun e he => by have := hI.hE e he; omega, ?_⟩
  rw [hI.hR]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h1 : x.val + d < t
  · have h2 : x.val + d < t + 1 := by omega
    simp [h1, h2]
  · have h2 : ¬ x.val + d < t + 1 := fun h => h1 (hiff x h)
    simp [h1, h2]

theorem inv_all (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (tie : TieRule n)
    (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    ∀ t, Inv d v ω t t (stateAfter d v tie ω t) := by
  intro t
  induction t with
  | zero => exact inv_init d v ω
  | succ t ih =>
    show Inv d v ω (t + 1) (t + 1) (period d v tie ω t (stateAfter d v tie ω t))
    obtain ⟨st1, hst1⟩ : ∃ x, x = (if h : t < n then arrive d v tie ⟨t, h⟩
        (stateAfter d v tie ω t) else stateAfter d v tie ω t) := ⟨_, rfl⟩
    have h1 : Inv d v ω (t + 1) t st1 := by
      rw [hst1]
      by_cases h : t < n
      · rw [dif_pos h]
        exact inv_arrive d v hv tie hTie ω t ⟨t, h⟩ rfl _ ih
      · rw [dif_neg h]
        exact inv_mono ih (Nat.le_succ t)
    have hper : period d v tie ω t (stateAfter d v tie ω t)
        = if h : d ≤ t ∧ t - d < n then critical ω ⟨t - d, h.2⟩ st1 else st1 := by
      subst hst1; rfl
    rw [hper]
    by_cases h2 : d ≤ t ∧ t - d < n
    · rw [dif_pos h2]
      exact inv_crit d v ω t ⟨t - d, h2.2⟩ (by show t - d + d = t; omega) st1 h1
    · rw [dif_neg h2]
      exact inv_nocrit d v ω (t + 1) t h2 st1 h1

theorem arrive_congr (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n)
    (st st' : State n) (hS : st.S = st'.S) (hm : st.m = st'.m) (hp : st.p = st'.p) :
    (arrive d v tie k st).S = (arrive d v tie k st').S ∧
    (arrive d v tie k st).m = (arrive d v tie k st').m ∧
    (arrive d v tie k st).p = (arrive d v tie k st').p := by
  obtain ⟨st0, h0⟩ : ∃ x, x = addVertex k st := ⟨_, rfl⟩
  obtain ⟨st0', h0'⟩ : ∃ x, x = addVertex k st' := ⟨_, rfl⟩
  have harr : arrive d v tie k st = bid d v tie k st0 := by rw [h0]; rfl
  have harr' : arrive d v tie k st' = bid d v tie k st0' := by rw [h0']; rfl
  have eS : st0.S = st0'.S := by
    rw [h0, h0']; show insert k st.S = insert k st'.S; rw [hS]
  have em : st0.m = st0'.m := by
    rw [h0, h0']; show Function.update st.m k none = Function.update st'.m k none; rw [hm]
  have ep : st0.p = st0'.p := by
    rw [h0, h0']; show Function.update st.p k 0 = Function.update st'.p k 0; rw [hp]
  have emarg : margins d v k st0 = margins d v k st0' := by
    funext x; unfold margins; rw [eS, ep]
  rw [harr, harr']
  refine ⟨by rw [bid_S, bid_S, eS], ?_, ?_⟩
  · by_cases hc : 0 < margins d v k st0 (tie k st0.S (margins d v k st0))
    · have hc' : 0 < margins d v k st0' (tie k st0'.S (margins d v k st0')) := by
        rw [← eS, ← emarg]; exact hc
      rw [bid_m_pos d v tie k st0 hc, bid_m_pos d v tie k st0' hc', em, eS, emarg]
    · have hc' : ¬ 0 < margins d v k st0' (tie k st0'.S (margins d v k st0')) := by
        rw [← eS, ← emarg]; exact hc
      rw [bid_m_neg d v tie k st0 hc, bid_m_neg d v tie k st0' hc', em]
  · by_cases hc : 0 < margins d v k st0 (tie k st0.S (margins d v k st0))
    · have hc' : 0 < margins d v k st0' (tie k st0'.S (margins d v k st0')) := by
        rw [← eS, ← emarg]; exact hc
      rw [bid_p_pos d v tie k st0 hc, bid_p_pos d v tie k st0' hc', ep, eS, emarg]
    · have hc' : ¬ 0 < margins d v k st0' (tie k st0'.S (margins d v k st0')) := by
        rw [← eS, ← emarg]; exact hc
      rw [bid_p_neg d v tie k st0 hc, bid_p_neg d v tie k st0' hc', ep]

theorem crit_congr (ω ω' : Fin n → Bool) (c : Fin n) (st st' : State n) (hS : st.S = st'.S)
    (hm : st.m = st'.m) (hp : st.p = st'.p) :
    (critical ω c st).S = (critical ω' c st').S ∧ (critical ω c st).m = (critical ω' c st').m ∧
    (critical ω c st).p = (critical ω' c st').p := by
  refine ⟨?_, by rw [crit_m, crit_m, hm], by rw [crit_p, crit_p, hp]⟩
  rcases h : st.m c with _ | l
  · have h' : st'.m c = none := by rw [← hm]; exact h
    rw [crit_none ω c st h, crit_none ω' c st' h', hS]
  · have h' : st'.m c = some l := by rw [← hm]; exact h
    rw [crit_S_some ω c st l h, crit_S_some ω' c st' l h', hS]

theorem period_congr (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (ω ω' : Fin n → Bool)
    (t : ℕ) (st st' : State n) (i1 : st.S = st'.S) (i2 : st.m = st'.m) (i3 : st.p = st'.p) :
    (period d v tie ω t st).S = (period d v tie ω' t st').S ∧
      (period d v tie ω t st).m = (period d v tie ω' t st').m ∧
      (period d v tie ω t st).p = (period d v tie ω' t st').p := by
  obtain ⟨a1, a2, a3⟩ : (if h : t < n then arrive d v tie ⟨t, h⟩ st else st).S =
        (if h : t < n then arrive d v tie ⟨t, h⟩ st' else st').S ∧
      (if h : t < n then arrive d v tie ⟨t, h⟩ st else st).m =
        (if h : t < n then arrive d v tie ⟨t, h⟩ st' else st').m ∧
      (if h : t < n then arrive d v tie ⟨t, h⟩ st else st).p =
        (if h : t < n then arrive d v tie ⟨t, h⟩ st' else st').p := by
    by_cases h : t < n
    · simp only [dif_pos h]; exact arrive_congr d v tie _ st st' i1 i2 i3
    · simp only [dif_neg h]; exact ⟨i1, i2, i3⟩
  have hper : ∀ (w : Fin n → Bool) (s : State n), period d v tie w t s =
      if h : d ≤ t ∧ t - d < n then critical w ⟨t - d, h.2⟩
        (if h : t < n then arrive d v tie ⟨t, h⟩ s else s)
      else (if h : t < n then arrive d v tie ⟨t, h⟩ s else s) := fun w s => rfl
  rw [hper ω st, hper ω' st']
  by_cases h2 : d ≤ t ∧ t - d < n
  · simp only [dif_pos h2]; exact crit_congr ω ω' _ _ _ a1 a2 a3
  · simp only [dif_neg h2]; exact ⟨a1, a2, a3⟩

theorem indep (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (ω ω' : Fin n → Bool) :
    ∀ t, (stateAfter d v tie ω t).S = (stateAfter d v tie ω' t).S ∧
      (stateAfter d v tie ω t).m = (stateAfter d v tie ω' t).m ∧
      (stateAfter d v tie ω t).p = (stateAfter d v tie ω' t).p := by
  intro t
  induction t with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    exact period_congr d v tie ω ω' t _ _ i1 i2 i3

def flipAt (k : Fin n) (ω : Fin n → Bool) : Fin n → Bool := Function.update ω k (!ω k)

theorem flipAt_invol (k : Fin n) : Function.Involutive (flipAt k) := by
  intro ω
  funext x
  by_cases hx : x = k
  · subst hx; simp [flipAt]
  · simp [flipAt, Function.update_of_ne hx]

theorem count_true (k : Fin n) :
    (Finset.univ.filter fun ω : Fin n → Bool => ω k = true).card = 2 ^ (n - 1) := by
  have hflip : (Finset.univ.filter fun ω : Fin n → Bool => ω k = true).card =
      (Finset.univ.filter fun ω : Fin n → Bool => ¬ ω k = true).card := by
    apply Finset.card_equiv (Function.Involutive.toPerm (flipAt k) (flipAt_invol k))
    intro ω
    simp [flipAt]
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun ω : Fin n → Bool => ω k = true)
  rw [← hflip, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.isLt; omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_succ] at htot
  omega

theorem count_seller (d : ℕ) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e) (tie : TieRule n)
    (hTie : IsArgmaxRule tie) (ω₀ : Fin n → Bool) :
    ∀ (N : ℕ) (k : Fin n), k.val < N → (finalState d v tie ω₀).m k ≠ none →
      (Finset.univ.filter fun ω : Fin n → Bool =>
        (finalState d v tie ω).status k = Status.seller).card = 2 ^ (n - 1) := by
  have hM : ∀ ω, (finalState d v tie ω).m = (finalState d v tie ω₀).m :=
    fun ω => (indep d v tie ω ω₀ (n + d)).2.1
  have hInv : ∀ ω, Inv d v ω (n + d) (n + d) (finalState d v tie ω) :=
    fun ω => inv_all d v hv tie hTie ω (n + d)
  intro N
  induction N with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ N ih =>
    intro k hk hmk
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hmk
    by_cases hp : ∃ j, (finalState d v tie ω₀).m j = some k
    · obtain ⟨j, hj⟩ := hp
      have hjk : j.val < k.val := ((hInv ω₀).hm j k hj).1
      have hjne : (finalState d v tie ω₀).m j ≠ none := by rw [hj]; simp
      have ihj := ih j (by omega) hjne
      have hcongr : (Finset.univ.filter fun ω : Fin n → Bool =>
          (finalState d v tie ω).status k = Status.seller) =
          (Finset.univ.filter fun ω : Fin n → Bool =>
          ¬ (finalState d v tie ω).status j = Status.seller) := by
        apply Finset.filter_congr
        intro ω _
        have hjω : (finalState d v tie ω).m j = some k := by rw [hM ω]; exact hj
        rcases (hInv ω).hJ j k (by have := j.isLt; omega) hjω with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
        · rw [h1, h2]; simp
        · rw [h1, h2]; simp
      rw [hcongr]
      have htot := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Bool)))
        (fun ω : Fin n → Bool => (finalState d v tie ω).status j = Status.seller)
      rw [ihj, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.isLt; omega⟩
      simp only [Nat.add_sub_cancel] at htot ⊢
      rw [pow_succ] at htot
      omega
    · have hcongr : (Finset.univ.filter fun ω : Fin n → Bool =>
          (finalState d v tie ω).status k = Status.seller) =
          (Finset.univ.filter fun ω : Fin n → Bool => ω k = true) := by
        apply Finset.filter_congr
        intro ω _
        exact (hInv ω).hL k l (by have := k.isLt; omega) (by rw [hM ω]; exact hl)
          (fun j _ hj => hp ⟨j, by rw [← hM ω]; exact hj⟩)
      rw [hcongr]
      exact count_true k

end Aux_WM_S3

open WindowedMatching in
theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (k l : Fin n)
    (hkl : (finalState d v tie ω).m k = some l) :
    ((finalState d v tie ω).status k = .seller ∧ (finalState d v tie ω).status l = .buyer ∧
      (k, l) ∈ (finalState d v tie ω).finalized) ∨
    ((finalState d v tie ω).status k = .buyer ∧ (finalState d v tie ω).status l = .seller ∧
      (k, l) ∉ (finalState d v tie ω).finalized) := by
  have hI : Aux_WM_S3.Inv d v ω (n + d) (n + d) (finalState d v tie ω) :=
    Aux_WM_S3.inv_all d v hv tie hTie ω (n + d)
  exact hI.hJ k l (by have := k.isLt; omega) hkl
