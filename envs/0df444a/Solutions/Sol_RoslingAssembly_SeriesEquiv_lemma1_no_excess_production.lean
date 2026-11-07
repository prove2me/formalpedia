-- Prove2me | solution 1 for RoslingAssembly.SeriesEquiv.lemma1_no_excess_production
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:19:05.548014+00:00
-- url     : https://prove2.me/submissions/4619484f-04da-4803-84fe-3d6a14525f4e

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv.ReduxAux
open RoslingAssembly.SeriesEquiv

theorem succStop_lt (S : Model) (hTree : S.ValidTree) (x : ℕ) (h1 : 1 ≤ x)
    (hx : x ≤ S.N) : S.succStop x < x := by
  unfold Model.succStop
  rw [if_neg (by omega)]
  rcases Nat.lt_or_ge x 2 with h | h
  · have : x = 1 := by omega
    subst this; rw [hTree.2.1]; omega
  · exact (hTree.2.2.1 x (Finset.mem_Icc.mpr ⟨h, hx⟩)).2

theorem succStop_zero (S : Model) : S.succStop 0 = 0 := by
  simp [Model.succStop]

theorem succStop_le (S : Model) (hTree : S.ValidTree) (x : ℕ)
    (hx : x ≤ S.N) : S.succStop x ≤ x := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; rw [succStop_zero]
  · exact (succStop_lt S hTree x h hx).le

theorem iter_bound (S : Model) (hTree : S.ValidTree) :
    ∀ n x, x ≤ S.N → S.succStop^[n] x + n ≤ x ∨ S.succStop^[n] x = 0 := by
  intro n
  induction n with
  | zero => intro x _; left; simp
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    rcases ih x hx with h | h
    · rcases Nat.eq_zero_or_pos (S.succStop^[n] x) with h0 | h0
      · right; rw [h0, succStop_zero]
      · left
        have := succStop_lt S hTree _ h0 (by omega)
        omega
    · right; rw [h, succStop_zero]

theorem mem_successors (S : Model) (x y : ℕ) :
    y ∈ S.successors x ↔
      (∃ n, 1 ≤ n ∧ n ≤ S.N ∧ S.succStop^[n] x = y) ∧ 1 ≤ y ∧ y ≤ S.N := by
  unfold Model.successors
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨n, ⟨h1, h2⟩, h3⟩, h4, h5⟩
    exact ⟨⟨n, h1, h2, h3.symm⟩, h4, h5⟩
  · rintro ⟨⟨n, h1, h2, h3⟩, h4, h5⟩
    exact ⟨⟨n, ⟨h1, h2⟩, h3.symm⟩, h4, h5⟩

theorem successors_lt (S : Model) (hTree : S.ValidTree) (x y : ℕ)
    (hx : x ≤ S.N) (hy : y ∈ S.successors x) : y < x := by
  rw [mem_successors] at hy
  obtain ⟨⟨n, h1, _, h3⟩, h4, _⟩ := hy
  rcases iter_bound S hTree n x hx with h | h <;> omega

theorem successors_step (S : Model) (hTree : S.ValidTree) (x : ℕ)
    (h1 : 1 ≤ x) (hx : x ≤ S.N) (hf : S.succStop x ≠ 0) :
    S.successors x = insert (S.succStop x) (S.successors (S.succStop x)) := by
  ext y
  rw [Finset.mem_insert, mem_successors, mem_successors]
  have hlt := succStop_lt S hTree x h1 hx
  constructor
  · rintro ⟨⟨n, hn1, hn2, hn3⟩, hy1, hy2⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · left; have : n = 1 := by omega
      subst this; simpa using hn3.symm
    · right
      refine ⟨⟨n - 1, by omega, by omega, ?_⟩, hy1, hy2⟩
      rw [← Function.iterate_succ_apply]
      have : (n - 1).succ = n := by omega
      rw [this]; exact hn3
  · rintro (h | ⟨⟨n, hn1, hn2, hn3⟩, hy1, hy2⟩)
    · subst h
      exact ⟨⟨1, le_refl 1, by omega, by simp⟩, by omega, by omega⟩
    · rcases Nat.lt_or_ge n S.N with h | h
      · refine ⟨⟨n + 1, by omega, by omega, ?_⟩, hy1, hy2⟩
        rw [Function.iterate_succ_apply]; exact hn3
      · exfalso
        have hn : n = S.N := by omega
        rcases iter_bound S hTree (n + 1) x hx with h' | h'
        · rw [Function.iterate_succ_apply, hn3] at h'; omega
        · rw [Function.iterate_succ_apply, hn3] at h'; omega

theorem successors_of_zero (S : Model) (hTree : S.ValidTree) (x : ℕ)
    (h1 : 1 ≤ x) (hx : x ≤ S.N) (hf : S.succStop x = 0) :
    S.successors x = ∅ := by
  ext y
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_successors]
  rintro ⟨⟨n, hn1, _, hn3⟩, hy1, _⟩
  have : S.succStop^[n] x = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply, hf, Function.iterate_fixed (succStop_zero S)]
  omega

theorem M_step (S : Model) (hTree : S.ValidTree) (x : ℕ)
    (h1 : 1 ≤ x) (hx : x ≤ S.N) :
    S.M x = S.lead x + S.M (S.succStop x) := by
  by_cases hf : S.succStop x = 0
  · rw [hf]
    unfold Model.M
    rw [if_neg (by omega), if_pos rfl, successors_of_zero S hTree x h1 hx hf]
    simp
  · have hlt := succStop_lt S hTree x h1 hx
    have hnot : S.succStop x ∉ S.successors (S.succStop x) := fun h =>
      (lt_irrefl _) (successors_lt S hTree _ _ (by omega) h)
    unfold Model.M
    rw [if_neg (by omega), if_neg hf, successors_step S hTree x h1 hx hf,
      Finset.sum_insert hnot]

theorem M_mono (S : Model) (hTree : S.ValidTree) (a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ S.N) : S.M a ≤ S.M b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
    have := hTree.2.2.2 (b + 1) (Finset.mem_Icc.mpr ⟨by omega, hb⟩)
    simp only [Nat.add_sub_cancel] at this
    exact (ih (by omega)).trans this

theorem L_le_lead (S : Model) (hTree : S.ValidTree) (i : ℕ) (h1 : 1 ≤ i)
    (hi : i ≤ S.N) : S.L i ≤ S.lead i := by
  unfold Model.L
  have hs := M_step S hTree i h1 hi
  have hlt := succStop_lt S hTree i h1 hi
  have hm := M_mono S hTree (S.succStop i) (i - 1) (by omega) (by omega)
  omega

theorem L_one (S : Model) (hTree : S.ValidTree) : S.L 1 = S.lead 1 := by
  unfold Model.L
  have hs := M_step S hTree 1 le_rfl hTree.1
  have h0 : S.succStop 1 = 0 := by simp [Model.succStop, hTree.2.1]
  rw [h0] at hs
  have hM0 : S.M 0 = 0 := by simp [Model.M]
  simp only [Nat.sub_self, hM0] at hs ⊢
  omega

theorem shift (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (x t s a : ℕ) (ha : a < t) :
    S.pos x0 π ω x t (s + a) =
      S.pos x0 π ω x (t - a) s - ∑ r ∈ Finset.Ico (t - a) t, ω (r - 1) := by
  unfold Model.pos
  by_cases h1 : s + a < t
  · rw [if_pos h1, if_pos (by omega)]
    have e : t - (s + a) = t - a - s := by omega
    rw [e, sub_sub, Finset.sum_Ico_consecutive _ (by omega) (by omega)]
  · rw [if_neg h1, if_neg (by omega)]
    have e : s + a - t + 1 = s - (t - a) + 1 := by omega
    rw [e, sub_sub, Finset.sum_Ico_consecutive _ (by omega) (by omega)]

theorem pos_zero (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (x t : ℕ) (ht : 1 ≤ t) : S.pos x0 π ω x t 0 = decision π ω x t := by
  unfold Model.pos
  rw [if_pos (by omega)]
  simp

theorem pos_one_one (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (x s : ℕ) (hs : 1 ≤ s) : S.pos x0 π ω x 1 s = x0 x s := by
  unfold Model.pos
  rw [if_neg (by omega)]
  have : s - 1 + 1 = s := by omega
  simp [this]

theorem pos_mono (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (x : ℕ) (hfeas : ∀ τ ≥ 1, S.pos x0 π ω x τ 1 ≤ decision π ω x τ)
    (hx0 : ∀ s ≥ 1, x0 x (s + 1) ≤ x0 x s) (t s : ℕ) (ht : 1 ≤ t) :
    S.pos x0 π ω x t (s + 1) ≤ S.pos x0 π ω x t s := by
  by_cases hs : s < t
  · have h1 := shift S x0 π ω x t 1 s hs
    have h0 := shift S x0 π ω x t 0 s hs
    rw [zero_add] at h0
    rw [show s + 1 = 1 + s by omega, h1, h0, pos_zero S x0 π ω x (t - s) (by omega)]
    have := hfeas (t - s) (by omega)
    linarith
  · unfold Model.pos
    rw [if_neg hs, if_neg (by omega)]
    have e : s + 1 - t + 1 = (s - t + 1) + 1 := by omega
    rw [e]
    have := hx0 (s - t + 1) (by omega)
    linarith


theorem iter_le (S : Model) (hTree : S.ValidTree) (n x : ℕ) (hx : x ≤ S.N) :
    S.succStop^[n] x ≤ x := by
  rcases iter_bound S hTree n x hx with h | h <;> omega

theorem iter_zero (S : Model) (n : ℕ) : S.succStop^[n] 0 = 0 :=
  Function.iterate_fixed (succStop_zero S) n

theorem iter_inj (S : Model) (hTree : S.ValidTree) (x : ℕ) (hx : x ≤ S.N)
    (n n' : ℕ) (h : S.succStop^[n] x = S.succStop^[n'] x)
    (h1 : 1 ≤ S.succStop^[n] x) : n = n' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have e : S.succStop^[n'] x = S.succStop^[n' - n] (S.succStop^[n] x) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    have hb := iter_bound S hTree (n' - n) (S.succStop^[n] x)
      ((iter_le S hTree n x hx).trans hx)
    rw [← e] at hb
    omega
  · have e : S.succStop^[n] x = S.succStop^[n - n'] (S.succStop^[n'] x) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    have hb := iter_bound S hTree (n - n') (S.succStop^[n'] x)
      ((iter_le S hTree n' x hx).trans hx)
    rw [← e] at hb
    omega

theorem M_one (S : Model) (hTree : S.ValidTree) : S.M 1 = S.lead 1 := by
  have hs := M_step S hTree 1 le_rfl hTree.1
  have h0 : S.succStop 1 = 0 := by simp [Model.succStop, hTree.2.1]
  have hM0 : S.M 0 = 0 := by simp [Model.M]
  rw [h0, hM0] at hs; omega

/-- Positions along a tree edge: the successor's position is dominated by the
predecessor's position over the additional lead time. -/
theorem edge_le (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hInitial : S.WellFormedInitial x0) (hF : S.PathFeasible x0 π ω)
    (c k : ℕ) (hc : c ∈ Finset.Icc 1 S.N) (hk : k ∈ S.predecessors c)
    (τ s : ℕ) (hτ : 1 ≤ τ) :
    S.pos x0 π ω c τ s ≤ S.pos x0 π ω k τ (s + S.lead k) := by
  by_cases hs : s < τ
  · have h1 : S.pos x0 π ω c τ s = S.pos x0 π ω c (τ - s) 0 -
        ∑ r ∈ Finset.Ico (τ - s) τ, ω (r - 1) := by
      have := shift S x0 π ω c τ 0 s hs; rwa [zero_add] at this
    have h2 := shift S x0 π ω k τ (S.lead k) s hs
    rw [h1, add_comm s, h2, pos_zero S x0 π ω c (τ - s) (by omega)]
    have := (hF (τ - s) (by omega) c hc).2 k hk
    linarith
  · unfold Model.pos
    rw [if_neg hs, if_neg (by omega)]
    have e : s + S.lead k - τ + 1 = (s - τ + 1) + S.lead k := by omega
    rw [e]
    have := hInitial.2 c hc k hk (s - τ + 1) (by omega)
    linarith

theorem root_le (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hTree : S.ValidTree) (hInitial : S.WellFormedInitial x0)
    (hF : S.PathFeasible x0 π ω) (τ : ℕ) (hτ : 1 ≤ τ) :
    ∀ k, 1 ≤ k → k ≤ S.N → ∀ s,
      S.pos x0 π ω 1 τ s ≤ S.pos x0 π ω k τ (s + (S.M k - S.M 1)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkN s
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      subst this; simp
    · have hsk := hTree.2.2.1 k (Finset.mem_Icc.mpr ⟨h, hkN⟩)
      set c := S.succ k with hcdef
      have hstop : S.succStop k = c := by
        unfold Model.succStop; rw [if_neg (by omega)]
      have hMk := M_step S hTree k (by omega) hkN
      rw [hstop] at hMk
      have hMc := M_mono S hTree 1 c hsk.1 (by omega)
      have h1 := ih c hsk.2 hsk.1 (by omega) s
      have hkp : k ∈ S.predecessors c :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hkN⟩, rfl⟩
      have h2 := edge_le S x0 π ω hInitial hF c k
        (Finset.mem_Icc.mpr ⟨hsk.1, by omega⟩) hkp τ (s + (S.M c - S.M 1)) hτ
      have e : s + (S.M c - S.M 1) + S.lead k = s + (S.M k - S.M 1) := by omega
      rw [e] at h2
      exact h1.trans h2

/-! ### The modified policy -/

noncomputable def tt (S : Model) (i t n : ℕ) : ℕ := t + (S.M i - S.M (S.succStop^[n] i))

noncomputable def Dsum (ω : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ r ∈ Finset.Ico a b, ω (r - 1)

noncomputable def mval (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ)
    (ω : ℕ → ℝ) : ℝ :=
  if h : (Finset.Ioc i S.N).Nonempty then
    (Finset.Ioc i S.N).inf' h (fun k => S.pos x0 π ω k t (S.M k - S.M i))
  else S.pos x0 π ω i t 1

noncomputable def cval (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ)
    (ω : ℕ → ℝ) : ℝ :=
  max (S.pos x0 π ω i t 1) (mval S x0 π i t ω)

noncomputable def wv (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ)
    (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => min (decision π ω i t) (cval S x0 π i t ω)
  | n + 1 => min (decision π ω (S.succStop^[n + 1] i) (tt S i t (n + 1)))
      (wv S x0 π i t ω n - Dsum ω (tt S i t n) (tt S i t (n + 1)))

def ext (k : ℕ) (h : Fin k → ℝ) : ℕ → ℝ := fun j => if hj : j < k then h ⟨j, hj⟩ else 0

def IsNode (S : Model) (i t b τ : ℕ) (n : ℕ) : Prop :=
  S.succStop^[n] i = b ∧ 1 ≤ b ∧ τ = tt S i t n

open Classical in
noncomputable def sig (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ) :
    Policy := fun k h b =>
  if hb : ∃ n, IsNode S i t b (k + 1) n then
    wv S x0 π i t (ext k h) (Nat.find hb) else π k h b

theorem decision_local (π : Policy) (ω ω' : ℕ → ℝ) (b τ : ℕ)
    (h : ∀ j < τ - 1, ω j = ω' j) : decision π ω b τ = decision π ω' b τ := by
  unfold decision; congr 1; funext j; exact h j j.2

theorem pos_local (S : Model) (x0 : InitialPositions) (π : Policy) (ω ω' : ℕ → ℝ)
    (b τ s : ℕ) (h : ∀ j < τ - 1, ω j = ω' j) :
    S.pos x0 π ω b τ s = S.pos x0 π ω' b τ s := by
  unfold Model.pos
  split_ifs with hs
  · rw [decision_local π ω ω' b (τ - s) (fun j hj => h j (by omega))]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr; rw [Finset.mem_Ico] at hr; exact h _ (by omega)
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr; rw [Finset.mem_Ico] at hr; exact h _ (by omega)

theorem Dsum_local (ω ω' : ℕ → ℝ) (a b : ℕ) (ha : 1 ≤ a)
    (h : ∀ j < b - 1, ω j = ω' j) : Dsum ω a b = Dsum ω' a b := by
  unfold Dsum
  apply Finset.sum_congr rfl
  intro r hr; rw [Finset.mem_Ico] at hr; exact h _ (by omega)

theorem tt_mono (S : Model) (hTree : S.ValidTree) (i t : ℕ) (hi : i ≤ S.N) (n : ℕ) :
    tt S i t n ≤ tt S i t (n + 1) := by
  unfold tt
  rw [Function.iterate_succ_apply']
  have hle := (iter_le S hTree n i hi).trans hi
  rcases Nat.eq_zero_or_pos (S.succStop^[n] i) with h0 | h0
  · rw [h0, succStop_zero]
  · have := M_step S hTree _ h0 hle
    omega

theorem tt_ge (S : Model) (hTree : S.ValidTree) (i t : ℕ) (hi : i ≤ S.N) (n : ℕ) :
    t ≤ tt S i t n := by unfold tt; omega

theorem mval_local (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ)
    (ω ω' : ℕ → ℝ) (h : ∀ j < t - 1, ω j = ω' j) :
    mval S x0 π i t ω = mval S x0 π i t ω' := by
  unfold mval
  split_ifs with hne
  · congr 1; funext k; exact pos_local S x0 π ω ω' k t _ h
  · exact pos_local S x0 π ω ω' i t 1 h

theorem cval_local (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ)
    (ω ω' : ℕ → ℝ) (h : ∀ j < t - 1, ω j = ω' j) :
    cval S x0 π i t ω = cval S x0 π i t ω' := by
  unfold cval
  rw [pos_local S x0 π ω ω' i t 1 h, mval_local S x0 π i t ω ω' h]

theorem wv_local (S : Model) (x0 : InitialPositions) (π : Policy) (hTree : S.ValidTree)
    (i t : ℕ) (hi : i ≤ S.N) (ht : 1 ≤ t) (ω ω' : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < tt S i t n - 1, ω j = ω' j) :
    wv S x0 π i t ω n = wv S x0 π i t ω' n := by
  induction n with
  | zero =>
    have e : tt S i t 0 = t := by simp [tt]
    rw [e] at h
    simp only [wv]
    rw [decision_local π ω ω' i t h, cval_local S x0 π i t ω ω' h]
  | succ n ih =>
    have hm := tt_mono S hTree i t hi n
    have hg := tt_ge S hTree i t hi n
    simp only [wv]
    rw [decision_local π ω ω' _ _ h, ih (fun j hj => h j (by omega)),
      Dsum_local ω ω' _ _ (by omega) h]

theorem node_unique (S : Model) (hTree : S.ValidTree) (i t b τ : ℕ) (hi : i ≤ S.N)
    (n n' : ℕ) (h : IsNode S i t b τ n) (h' : IsNode S i t b τ n') : n = n' :=
  iter_inj S hTree i hi n n' (h.1.trans h'.1.symm) (h.1 ▸ h.2.1)

theorem node_time_unique (S : Model) (hTree : S.ValidTree) (i t b τ τ' : ℕ)
    (hi : i ≤ S.N) (n n' : ℕ) (h : IsNode S i t b τ n) (h' : IsNode S i t b τ' n') :
    τ = τ' := by
  have := iter_inj S hTree i hi n n' (h.1.trans h'.1.symm) (h.1 ▸ h.2.1)
  subst this
  rw [h.2.2, h'.2.2]

open Classical in
theorem dsig_node (S : Model) (x0 : InitialPositions) (π : Policy) (hTree : S.ValidTree)
    (i t : ℕ) (hi : i ≤ S.N) (ht : 1 ≤ t) (ω : ℕ → ℝ) (b τ n : ℕ) (hτ : 1 ≤ τ)
    (hn : IsNode S i t b τ n) :
    decision (sig S x0 π i t) ω b τ = wv S x0 π i t ω n := by
  unfold decision sig
  have hb : ∃ n, IsNode S i t b (τ - 1 + 1) n := ⟨n, by
    rw [Nat.sub_add_cancel hτ]; exact hn⟩
  rw [dif_pos hb]
  have hfind := Nat.find_spec hb
  rw [node_unique S hTree i t b (τ - 1 + 1) hi _ n hfind
    (by rw [Nat.sub_add_cancel hτ]; exact hn)]
  apply wv_local S x0 π hTree i t hi ht
  intro j hj
  rw [← hn.2.2] at hj
  simp [ext, hj]

open Classical in
theorem dsig_nonnode (S : Model) (x0 : InitialPositions) (π : Policy)
    (i t : ℕ) (ω : ℕ → ℝ) (b τ : ℕ) (hτ : 1 ≤ τ)
    (hn : ¬ ∃ n, IsNode S i t b τ n) :
    decision (sig S x0 π i t) ω b τ = decision π ω b τ := by
  unfold decision sig
  rw [dif_neg (by rw [Nat.sub_add_cancel hτ]; exact hn)]

theorem tt_zero (S : Model) (i t : ℕ) : tt S i t 0 = t := by simp [tt]

theorem succStop_of_pos (S : Model) (x : ℕ) (hx : 1 ≤ x) : S.succStop x = S.succ x := by
  unfold Model.succStop; rw [if_neg (by omega)]

theorem chain_step (S : Model) (hTree : S.ValidTree) (i t : ℕ) (hi : i ≤ S.N) (n : ℕ)
    (h1 : 1 ≤ S.succStop^[n + 1] i) :
    1 ≤ S.succStop^[n] i ∧ S.succStop^[n] i ≤ S.N ∧
    S.succStop^[n] i ∈ S.predecessors (S.succStop^[n + 1] i) ∧
    tt S i t (n + 1) = tt S i t n + S.lead (S.succStop^[n] i) := by
  have hle := (iter_le S hTree n i hi).trans hi
  have hpos : 1 ≤ S.succStop^[n] i := by
    by_contra hc
    have h0 : S.succStop^[n] i = 0 := by omega
    rw [Function.iterate_succ_apply', h0, succStop_zero] at h1; omega
  have hst : S.succStop^[n + 1] i = S.succ (S.succStop^[n] i) := by
    rw [Function.iterate_succ_apply', succStop_of_pos S _ hpos]
  refine ⟨hpos, hle, ?_, ?_⟩
  · rw [hst]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩, rfl⟩
  · have hM := M_step S hTree _ hpos hle
    have e : S.succStop (S.succStop^[n] i) = S.succStop^[n + 1] i :=
      (Function.iterate_succ_apply' _ _ _).symm
    rw [e] at hM
    have hMi := M_mono S hTree _ i (iter_le S hTree n i hi) hi
    unfold tt; omega

theorem wv_le (S : Model) (x0 : InitialPositions) (π : Policy) (i t : ℕ)
    (ω : ℕ → ℝ) (n : ℕ) :
    wv S x0 π i t ω n ≤ decision π ω (S.succStop^[n] i) (tt S i t n) := by
  cases n with
  | zero => simp only [wv, tt_zero, Function.iterate_zero, id]; exact min_le_left _ _
  | succ n => simp only [wv]; exact min_le_left _ _

theorem dsig_le (S : Model) (x0 : InitialPositions) (π : Policy) (hTree : S.ValidTree)
    (i t : ℕ) (hi : i ≤ S.N) (ht : 1 ≤ t) (ω : ℕ → ℝ) (b τ : ℕ) (hτ : 1 ≤ τ) :
    decision (sig S x0 π i t) ω b τ ≤ decision π ω b τ := by
  by_cases hn : ∃ n, IsNode S i t b τ n
  · obtain ⟨n, hn⟩ := hn
    rw [dsig_node S x0 π hTree i t hi ht ω b τ n hτ hn]
    have := wv_le S x0 π i t ω n
    rw [hn.1, ← hn.2.2] at this
    exact this
  · rw [dsig_nonnode S x0 π i t ω b τ hτ hn]

theorem pos_sig_le (S : Model) (x0 : InitialPositions) (π : Policy) (hTree : S.ValidTree)
    (i t : ℕ) (hi : i ≤ S.N) (ht : 1 ≤ t) (ω : ℕ → ℝ) (x τ s : ℕ) :
    S.pos x0 (sig S x0 π i t) ω x τ s ≤ S.pos x0 π ω x τ s := by
  unfold Model.pos
  split_ifs with hs
  · have := dsig_le S x0 π hTree i t hi ht ω x (τ - s) (by omega)
    linarith
  · exact le_rfl

theorem pos_sig_of_lt (S : Model) (x0 : InitialPositions) (σ : Policy) (ω : ℕ → ℝ)
    (x τ s : ℕ) (hs : s < τ) :
    S.pos x0 σ ω x τ s = decision σ ω x (τ - s) - Dsum ω (τ - s) τ := by
  unfold Model.pos Dsum; rw [if_pos hs]

theorem pos_policy_indep (S : Model) (x0 : InitialPositions) (σ π : Policy) (ω : ℕ → ℝ)
    (x τ s : ℕ) (hs : τ ≤ s) :
    S.pos x0 σ ω x τ s = S.pos x0 π ω x τ s := by
  unfold Model.pos; rw [if_neg (by omega), if_neg (by omega)]

section Feas
variable (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
  (hTree : S.ValidTree) (hInitial : S.WellFormedInitial x0)
  (hF : S.PathFeasible x0 π ω) (i t : ℕ) (hi1 : 1 ≤ i) (hiN : i < S.N) (ht : 1 ≤ t)
include hTree hInitial hF hi1 hiN ht

theorem cval_ge : S.pos x0 π ω i t 1 ≤ cval S x0 π i t ω := le_max_left _ _

theorem wv_lower (n : ℕ) (hn : 1 ≤ S.succStop^[n] i) :
    S.pos x0 π ω (S.succStop^[n] i) (tt S i t n) 1 ≤ wv S x0 π i t ω n := by
  induction n with
  | zero =>
    simp only [wv, tt_zero, Function.iterate_zero, id]
    apply le_min
    · exact (hF t ht i (Finset.mem_Icc.mpr ⟨hi1, hiN.le⟩)).1
    · exact cval_ge S x0 π ω hTree hInitial hF i t hi1 hiN ht
  | succ n ih =>
    obtain ⟨hp, hle, hpred, htt⟩ := chain_step S hTree i t hiN.le n hn
    have ih' := ih hp
    have hbN := (iter_le S hTree (n + 1) i hiN.le).trans hiN.le
    simp only [wv]
    apply le_min
    · exact (hF _ (by have := tt_ge S hTree i t hiN.le (n + 1); omega) _
        (Finset.mem_Icc.mpr ⟨hn, hbN⟩)).1
    · have he := edge_le S x0 π ω hInitial hF _ _ (Finset.mem_Icc.mpr ⟨hn, hbN⟩) hpred
        (tt S i t (n + 1)) 1 (by have := tt_ge S hTree i t hiN.le (n + 1); omega)
      have hs := shift S x0 π ω (S.succStop^[n] i) (tt S i t (n + 1)) 1
        (S.lead (S.succStop^[n] i)) (by have := tt_ge S hTree i t hiN.le n; omega)
      rw [hs] at he
      have e : tt S i t (n + 1) - S.lead (S.succStop^[n] i) = tt S i t n := by omega
      rw [e] at he
      unfold Dsum
      linarith

theorem wv_formula (n : ℕ) (hn : 1 ≤ S.succStop^[n] i) :
    wv S x0 π i t ω n = min (decision π ω (S.succStop^[n] i) (tt S i t n))
      (cval S x0 π i t ω - Dsum ω t (tt S i t n)) := by
  induction n with
  | zero => simp [wv, tt_zero, Dsum]
  | succ n ih =>
    obtain ⟨hp, hle, hpred, htt⟩ := chain_step S hTree i t hiN.le n hn
    have hbN := (iter_le S hTree (n + 1) i hiN.le).trans hiN.le
    have hg := tt_ge S hTree i t hiN.le n
    simp only [wv]
    rw [ih hp]
    -- feasibility: the successor's order is below the predecessor's
    have hup := (hF (tt S i t (n + 1)) (by omega) _
      (Finset.mem_Icc.mpr ⟨hn, hbN⟩)).2 _ hpred
    have hs := pos_sig_of_lt S x0 π ω (S.succStop^[n] i) (tt S i t (n + 1))
      (S.lead (S.succStop^[n] i)) (by omega)
    have e : tt S i t (n + 1) - S.lead (S.succStop^[n] i) = tt S i t n := by omega
    rw [hs, e] at hup
    have hsplit : Dsum ω t (tt S i t n) + Dsum ω (tt S i t n) (tt S i t (n + 1)) =
        Dsum ω t (tt S i t (n + 1)) := Finset.sum_Ico_consecutive _ hg (by omega)
    rw [← min_sub_sub_right]
    apply le_antisymm
    · apply le_min
      · exact min_le_left _ _
      · refine (min_le_right _ _).trans ?_
        refine (min_le_right _ _).trans ?_
        linarith
    · apply le_min
      · exact min_le_left _ _
      · apply le_min
        · exact (min_le_left _ _).trans hup
        · refine (min_le_right _ _).trans ?_
          linarith

theorem dsig_one (τ : ℕ) (hτ : 1 ≤ τ) :
    decision (sig S x0 π i t) ω 1 τ = decision π ω 1 τ := by
  by_cases hn : ∃ n, IsNode S i t 1 τ n
  · obtain ⟨n, hn⟩ := hn
    rw [dsig_node S x0 π hTree i t hiN.le ht ω 1 τ n hτ hn,
      wv_formula S x0 π ω hTree hInitial hF i t hi1 hiN ht n (by rw [hn.1])]
    rw [hn.1, ← hn.2.2]
    apply min_eq_left
    -- the end item's order is limited by every later item
    have hne : (Finset.Ioc i S.N).Nonempty := ⟨i + 1, Finset.mem_Ioc.mpr ⟨by omega, hiN⟩⟩
    have hm : mval S x0 π i t ω ≤ cval S x0 π i t ω := le_max_right _ _
    unfold mval at hm
    rw [dif_pos hne] at hm
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hne
      (fun k => S.pos x0 π ω k t (S.M k - S.M i))
    rw [hkeq] at hm
    have hk' := Finset.mem_Ioc.mp hk
    have hM1 := M_mono S hTree 1 i hi1 hiN.le
    have hMk := M_mono S hTree i k hk'.1.le hk'.2
    have hτe : τ = t + (S.M i - S.M 1) := by rw [hn.2.2]; unfold tt; rw [hn.1]
    have hr := root_le S x0 π ω hTree hInitial hF τ hτ k (by omega) hk'.2 0
    rw [pos_zero S x0 π ω 1 τ hτ, zero_add] at hr
    have e : S.M k - S.M 1 = (S.M k - S.M i) + (S.M i - S.M 1) := by omega
    rw [e, shift S x0 π ω k τ _ _ (by omega)] at hr
    have e2 : τ - (S.M i - S.M 1) = t := by omega
    rw [e2] at hr
    unfold Dsum
    rw [hτe] at hr ⊢
    linarith
  · rw [dsig_nonnode S x0 π i t ω 1 τ hτ hn]

theorem sig_feasible : S.PathFeasible x0 (sig S x0 π i t) ω := by
  intro τ hτ b hb
  have hb' := Finset.mem_Icc.mp hb
  constructor
  · -- lower constraint
    by_cases hn : ∃ n, IsNode S i t b τ n
    · obtain ⟨n, hn⟩ := hn
      rw [dsig_node S x0 π hTree i t hiN.le ht ω b τ n hτ hn]
      have hlow := wv_lower S x0 π ω hTree hInitial hF i t hi1 hiN ht n (by rw [hn.1]; exact hb'.1)
      rw [hn.1, ← hn.2.2] at hlow
      refine le_trans ?_ hlow
      by_cases h1 : 1 < τ
      · rw [pos_sig_of_lt S x0 _ ω b τ 1 h1, pos_sig_of_lt S x0 π ω b τ 1 h1]
        have : ¬ ∃ n', IsNode S i t b (τ - 1) n' := by
          rintro ⟨n', hn'⟩
          have := node_time_unique S hTree i t b τ (τ - 1) hiN.le n n' hn hn'
          omega
        rw [dsig_nonnode S x0 π i t ω b (τ - 1) (by omega) this]
      · exact le_of_eq (pos_policy_indep S x0 _ π ω b τ 1 (by omega))
    · rw [dsig_nonnode S x0 π i t ω b τ hτ hn]
      exact (pos_sig_le S x0 π hTree i t hiN.le ht ω b τ 1).trans (hF τ hτ b hb).1
  · intro k hk
    have hkI := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    by_cases hc : S.lead k < τ ∧ ∃ n, IsNode S i t k (τ - S.lead k) n
    · obtain ⟨hlt, n, hn⟩ := hc
      -- the next chain node is (b, τ)
      have hsk : S.succ k = b := (Finset.mem_filter.mp hk).2
      have hnext : S.succStop^[n + 1] i = b := by
        rw [Function.iterate_succ_apply', hn.1, succStop_of_pos S k (by omega)]; exact hsk
      obtain ⟨_, _, _, htt⟩ := chain_step S hTree i t hiN.le n (by rw [hnext]; exact hb'.1)
      rw [hn.1] at htt
      have hτn : τ = tt S i t (n + 1) := by rw [htt, ← hn.2.2]; omega
      have hnode : IsNode S i t b τ (n + 1) := ⟨hnext, hb'.1, hτn⟩
      rw [dsig_node S x0 π hTree i t hiN.le ht ω b τ (n + 1) hτ hnode,
        pos_sig_of_lt S x0 _ ω k τ _ hlt,
        dsig_node S x0 π hTree i t hiN.le ht ω k (τ - S.lead k) n (by omega) hn]
      simp only [wv]
      refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [← hn.2.2, ← hτn]
    · have hpos : S.pos x0 (sig S x0 π i t) ω k τ (S.lead k) =
          S.pos x0 π ω k τ (S.lead k) := by
        by_cases hlt : S.lead k < τ
        · have hnn : ¬ ∃ n, IsNode S i t k (τ - S.lead k) n := fun h => hc ⟨hlt, h⟩
          rw [pos_sig_of_lt S x0 _ ω k τ _ hlt, pos_sig_of_lt S x0 π ω k τ _ hlt,
            dsig_nonnode S x0 π i t ω k _ (by omega) hnn]
        · exact pos_policy_indep S x0 _ π ω k τ _ (by omega)
      rw [hpos]
      exact (dsig_le S x0 π hTree i t hiN.le ht ω b τ hτ).trans ((hF τ hτ b hb).2 k hk)

end Feas

theorem pc_le (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hTree : S.ValidTree) (hInitial : S.WellFormedInitial x0)
    (hF : S.PathFeasible x0 π ω) (hα : 0 < S.α) (hAss : S.Assumption)
    (i t : ℕ) (hi1 : 1 ≤ i) (hiN : i < S.N) (ht : 1 ≤ t) (τ : ℕ) (hτ : 1 ≤ τ) :
    S.periodCost (sig S x0 π i t) ω τ ≤ S.periodCost π ω τ := by
  unfold Model.periodCost
  rw [dsig_one S x0 π ω hTree hInitial hF i t hi1 hiN ht τ hτ]
  gcongr with b hb
  · have := hAss.1 b hb
    positivity
  · exact dsig_le S x0 π hTree i t hiN.le ht ω b τ hτ

theorem pc_lt (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hTree : S.ValidTree) (hInitial : S.WellFormedInitial x0)
    (hF : S.PathFeasible x0 π ω) (hα : 0 < S.α) (hAss : S.Assumption)
    (i t : ℕ) (hi1 : 1 ≤ i) (hiN : i < S.N) (ht : 1 ≤ t)
    (hlt : wv S x0 π i t ω 0 < decision π ω i t) :
    S.periodCost (sig S x0 π i t) ω t < S.periodCost π ω t := by
  unfold Model.periodCost
  rw [dsig_one S x0 π ω hTree hInitial hF i t hi1 hiN ht t ht]
  apply add_lt_add_of_lt_of_le _ le_rfl
  apply Finset.sum_lt_sum
  · intro b hb
    have := hAss.1 b hb
    have h2 := dsig_le S x0 π hTree i t hiN.le ht ω b t ht
    have : 0 ≤ S.α ^ S.lead b * S.h b := by positivity
    exact mul_le_mul_of_nonneg_left h2 this
  · refine ⟨i, Finset.mem_Icc.mpr ⟨hi1, hiN.le⟩, ?_⟩
    have hnode : IsNode S i t i t 0 := ⟨rfl, hi1, by simp [tt]⟩
    rw [dsig_node S x0 π hTree i t hiN.le ht ω i t 0 ht hnode]
    have := hAss.1 i (Finset.mem_Icc.mpr ⟨hi1, hiN.le⟩)
    have : 0 < S.α ^ S.lead i * S.h i := by positivity
    exact mul_lt_mul_of_pos_left hlt this

theorem minLater_eq (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (i t : ℕ) (hne : (Finset.Ioc i S.N).Nonempty) :
    S.minLater x0 π ω i t =
      (((Finset.Ioc i S.N).inf' hne (fun k => S.pos x0 π ω k t (S.M k - S.M i)) : ℝ)
        : WithTop ℝ) := by
  unfold Model.minLater
  apply le_antisymm
  · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hne
      (fun k => S.pos x0 π ω k t (S.M k - S.M i))
    rw [hkeq]
    exact Finset.inf_le (f := fun k =>
      ((S.pos x0 π ω k t (S.M k - S.M i) : ℝ) : WithTop ℝ)) hk
  · apply Finset.le_inf
    intro k hk
    exact WithTop.coe_le_coe.mpr (Finset.inf'_le _ hk)

theorem noExcess_of_le (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (i t : ℕ) (hiN : i < S.N)
    (hXY : S.pos x0 π ω i t 1 ≤ decision π ω i t)
    (hle : decision π ω i t ≤ cval S x0 π i t ω) : S.NoExcessAt x0 π ω i t := by
  have hne : (Finset.Ioc i S.N).Nonempty := ⟨i + 1, Finset.mem_Ioc.mpr ⟨by omega, hiN⟩⟩
  unfold cval mval at hle
  rw [dif_pos hne] at hle
  unfold Model.NoExcessAt
  rw [minLater_eq S x0 π ω i t hne]
  constructor
  · intro h
    have h' := WithTop.coe_le_coe.mp h
    rw [max_eq_left h'] at hle
    linarith
  · intro h
    have h' := WithTop.coe_le_coe.mp h
    rw [max_eq_right h'] at hle
    exact WithTop.coe_le_coe.mpr hle

theorem noExcess_last (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (t : ℕ) : S.NoExcessAt x0 π ω S.N t := by
  unfold Model.NoExcessAt Model.minLater
  rw [Finset.Ioc_self, Finset.inf_empty]
  exact ⟨fun h => absurd h (not_le.mpr (WithTop.coe_lt_top _)), fun _ => le_top⟩

/-! ### Measure-theoretic estimates -/
open MeasureTheory

theorem fin_lemma (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun x : ℝ => x) ν) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (f : ℕ → (ℕ → ℝ) → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν),
      ∀ k, f k ω ≤ A + B * ∑ j ∈ Finset.range k, |ω j|) :
    ∫⁻ ω, ∑' k, ENNReal.ofReal (α ^ k * f k ω) ∂(Measure.infinitePi fun _ : ℕ => ν)
      < ⊤ := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  set I := ∫⁻ x, ENNReal.ofReal |x| ∂ν with hIdef
  have hI : I < ⊤ := by
    have := hInt.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    simpa [Real.enorm_eq_ofReal_abs] using this
  have hmeasabs : Measurable (fun x : ℝ => ENNReal.ofReal |x|) :=
    ENNReal.measurable_ofReal.comp measurable_abs
  have hIj : ∀ j, ∫⁻ ω, ENNReal.ofReal |ω j| ∂μ = I := fun j =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).lintegral_comp hmeasabs
  set I' := I.toReal
  have hII : ENNReal.ofReal I' = I := ENNReal.ofReal_toReal hI.ne
  have hI'0 : 0 ≤ I' := ENNReal.toReal_nonneg
  have hmeasS : ∀ k, Measurable (fun ω : ℕ → ℝ => ∑ j ∈ Finset.range k, |ω j|) :=
    fun k => Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).abs)
  have hterm : ∀ k, ∫⁻ ω, ENNReal.ofReal (α ^ k * (A + B * ∑ j ∈ Finset.range k, |ω j|)) ∂μ
      ≤ ENNReal.ofReal (α ^ k * A + (k : ℝ) * α ^ k * B * I') := by
    intro k
    have hak : 0 ≤ α ^ k := pow_nonneg hα.1.le k
    calc ∫⁻ ω, ENNReal.ofReal (α ^ k * (A + B * ∑ j ∈ Finset.range k, |ω j|)) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (α ^ k * A) +
            ∑ j ∈ Finset.range k, ENNReal.ofReal (α ^ k * B) * ENNReal.ofReal |ω j|) ∂μ := by
          apply lintegral_mono
          intro ω
          dsimp only
          have e : α ^ k * (A + B * ∑ j ∈ Finset.range k, |ω j|) =
              α ^ k * A + ∑ j ∈ Finset.range k, (α ^ k * B) * |ω j| := by
            rw [Finset.mul_sum, mul_add, Finset.mul_sum]
            congr 1; apply Finset.sum_congr rfl; intro j _; ring
          rw [e]
          refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg hak hB) (abs_nonneg _))]
          apply le_of_eq
          apply Finset.sum_congr rfl
          intro j _
          rw [ENNReal.ofReal_mul (mul_nonneg hak hB)]
      _ = ENNReal.ofReal (α ^ k * A) +
            ∑ j ∈ Finset.range k, ENNReal.ofReal (α ^ k * B) * I := by
          have hmj : ∀ j ∈ Finset.range k, Measurable (fun ω : ℕ → ℝ =>
              ENNReal.ofReal (α ^ k * B) * ENNReal.ofReal |ω j|) :=
            fun j _ => (hmeasabs.comp (measurable_pi_apply j)).const_mul _
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_finset_sum _ hmj]
          simp only [measure_univ, mul_one]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hIj]
      _ = ENNReal.ofReal (α ^ k * A + (k : ℝ) * α ^ k * B * I') := by
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          rw [ENNReal.ofReal_add (mul_nonneg hak hA)
            (mul_nonneg (mul_nonneg (mul_nonneg hk0 hak) hB) hI'0)]
          congr 1
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hII,
            ← ENNReal.ofReal_mul (mul_nonneg hak hB), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul hk0]
          congr 1; ring
  have hsum : Summable (fun k : ℕ => α ^ k * A + (k : ℝ) * α ^ k * B * I') := by
    have h1 : Summable (fun k : ℕ => α ^ k) :=
      summable_geometric_of_lt_one hα.1.le hα.2
    have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * α ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_pos hα.1]; exact hα.2)
    refine (h1.mul_right A).add ((h2.mul_right (B * I')).congr ?_)
    intro k; simp; ring
  calc ∫⁻ ω, ∑' k, ENNReal.ofReal (α ^ k * f k ω) ∂μ
      ≤ ∫⁻ ω, ∑' k, ENNReal.ofReal (α ^ k * (A + B * ∑ j ∈ Finset.range k, |ω j|)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hf] with ω hω
        apply ENNReal.tsum_le_tsum
        intro k
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (hω k) (pow_nonneg hα.1.le k)
    _ = ∑' k, ∫⁻ ω, ENNReal.ofReal (α ^ k * (A + B * ∑ j ∈ Finset.range k, |ω j|)) ∂μ := by
        rw [lintegral_tsum]
        intro k
        exact (ENNReal.measurable_ofReal.comp
          ((measurable_const.add ((hmeasS k).const_mul B)).const_mul _)).aemeasurable
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (α ^ k * A + (k : ℝ) * α ^ k * B * I') :=
        ENNReal.tsum_le_tsum hterm
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => add_nonneg
          (mul_nonneg (pow_nonneg hα.1.le k) hA)
          (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hα.1.le k)) hB)
            hI'0)) hsum]
        exact ENNReal.ofReal_lt_top

/-- The expected shortage function. -/
noncomputable def gS (S : Model) (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂S.leadDemandLaw

theorem integ_shift (L : Measure ℝ) [IsFiniteMeasure L] (y y' : ℝ)
    (h : Integrable (fun x => max (x - y) 0) L) :
    Integrable (fun x => max (x - y') 0) L := by
  refine (h.add (integrable_const |y - y'|)).mono' ?_ ?_
  · exact ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [le_max_left (x - y) 0, le_abs_self (y - y')]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)

theorem gS_anti (S : Model) [IsFiniteMeasure S.leadDemandLaw] : Antitone (gS S) := by
  intro y y' hyy
  unfold gS
  by_cases hI : Integrable (fun x => max (x - y) 0) S.leadDemandLaw
  · exact integral_mono (integ_shift _ y y' hI) hI
      (fun x => max_le_max (by linarith) le_rfl)
  · have hI' : ¬ Integrable (fun x => max (x - y') 0) S.leadDemandLaw :=
      fun h => hI (integ_shift _ y' y h)
    rw [integral_undef hI, integral_undef hI']

theorem gS_nonneg (S : Model) (y : ℝ) : 0 ≤ gS S y :=
  integral_nonneg (fun x => le_max_right _ _)

theorem gS_bound (S : Model) [IsFiniteMeasure S.leadDemandLaw] (y : ℝ) :
    gS S y ≤ gS S 0 + |y| * S.leadDemandLaw.real Set.univ := by
  unfold gS
  by_cases hI : Integrable (fun x => max (x - 0) 0) S.leadDemandLaw
  · have hIy := integ_shift _ 0 y hI
    calc ∫ x, max (x - y) 0 ∂S.leadDemandLaw
        ≤ ∫ x, (max (x - 0) 0 + |y|) ∂S.leadDemandLaw := by
          apply integral_mono hIy (hI.add (integrable_const _))
          intro x
          simp only [Pi.add_apply]
          apply max_le
          · linarith [le_max_left (x - 0) 0, neg_abs_le y]
          · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
      _ = _ := by
          rw [integral_add hI (integrable_const _), integral_const, smul_eq_mul]
          ring
  · have hIy : ¬ Integrable (fun x => max (x - y) 0) S.leadDemandLaw :=
      fun h => hI (integ_shift _ y 0 h)
    rw [integral_undef hI, integral_undef hIy]
    have : 0 ≤ S.leadDemandLaw.real Set.univ := measureReal_nonneg
    positivity

theorem meas_decision (π : Policy) (hπ : MeasurablePolicy π) (b τ : ℕ) :
    Measurable (fun ω : ℕ → ℝ => decision π ω b τ) := by
  unfold decision
  exact (hπ (τ - 1) b).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply _))

theorem meas_pos (S : Model) (x0 : InitialPositions) (π : Policy) (hπ : MeasurablePolicy π)
    (b τ s : ℕ) : Measurable (fun ω => S.pos x0 π ω b τ s) := by
  by_cases hs : s < τ
  · simp only [Model.pos, hs, if_true]
    exact (meas_decision π hπ b _).sub
      (Finset.measurable_sum _ (fun r _ => measurable_pi_apply _))
  · simp only [Model.pos, hs, if_false]
    exact measurable_const.sub (Finset.measurable_sum _ (fun r _ => measurable_pi_apply _))

theorem meas_pc (S : Model) [IsFiniteMeasure S.leadDemandLaw] (π : Policy)
    (hπ : MeasurablePolicy π) (τ : ℕ) : Measurable (fun ω => S.periodCost π ω τ) := by
  unfold Model.periodCost
  refine (Finset.measurable_sum _ (fun b _ => (meas_decision π hπ b τ).const_mul _)).add ?_
  exact ((gS_anti S).measurable.comp (meas_decision π hπ 1 τ)).const_mul _

theorem meas_inf' {s : Finset ℕ} (hs : s.Nonempty) (f : ℕ → (ℕ → ℝ) → ℝ)
    (hf : ∀ k, Measurable (f k)) : Measurable (fun ω => s.inf' hs (fun k => f k ω)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a
  | cons a s ha hs ih =>
    simp only [Finset.inf'_cons hs]
    exact (hf a).inf ih

theorem meas_mval (S : Model) (x0 : InitialPositions) (π : Policy) (hπ : MeasurablePolicy π)
    (i t : ℕ) : Measurable (mval S x0 π i t) := by
  unfold mval
  by_cases hne : (Finset.Ioc i S.N).Nonempty
  · simp only [hne, dif_pos]
    exact meas_inf' hne (fun k ω => S.pos x0 π ω k t (S.M k - S.M i))
      (fun k => meas_pos S x0 π hπ k t _)
  · simp only [hne, dif_neg, not_false_eq_true]
    exact meas_pos S x0 π hπ i t 1

theorem meas_wv (S : Model) (x0 : InitialPositions) (π : Policy) (hπ : MeasurablePolicy π)
    (i t : ℕ) (n : ℕ) : Measurable (fun ω => wv S x0 π i t ω n) := by
  induction n with
  | zero =>
    simp only [wv, cval]
    exact (meas_decision π hπ i t).min ((meas_pos S x0 π hπ i t 1).max (meas_mval S x0 π hπ i t))
  | succ n ih =>
    simp only [wv]
    exact (meas_decision π hπ _ _).min (ih.sub
      (Finset.measurable_sum _ (fun r _ => measurable_pi_apply _)))

theorem meas_ext (k : ℕ) : Measurable (ext k) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j < k
  · simp only [ext, hj, dif_pos]
    exact measurable_pi_apply _
  · simp only [ext, hj, dif_neg, not_false_eq_true]
    exact measurable_const

open Classical in
theorem meas_sig (S : Model) (x0 : InitialPositions) (π : Policy) (hπ : MeasurablePolicy π)
    (i t : ℕ) : MeasurablePolicy (sig S x0 π i t) := by
  intro k b
  by_cases hb : ∃ n, IsNode S i t b (k + 1) n
  · simp only [sig, hb, dif_pos]
    exact (meas_wv S x0 π hπ i t _).comp (meas_ext k)
  · simp only [sig, hb, dif_neg, not_false_eq_true]
    exact hπ k b

/-! ### Cost comparison -/

theorem ofReal_max0 (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem max_sub_max (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem pair_le (x y : ℝ) (h : x ≤ y) :
    ENNReal.ofReal x + ENNReal.ofReal (-y) ≤ ENNReal.ofReal y + ENNReal.ofReal (-x) := by
  rw [ofReal_max0 x, ofReal_max0 (-y), ofReal_max0 y, ofReal_max0 (-x),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have := max_sub_max x; have := max_sub_max y
  linarith

theorem pair_lt (x y : ℝ) (h : x < y) :
    ENNReal.ofReal x + ENNReal.ofReal (-y) < ENNReal.ofReal y + ENNReal.ofReal (-x) := by
  rw [ofReal_max0 x, ofReal_max0 (-y), ofReal_max0 y, ofReal_max0 (-x),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  have hpos : 0 < max y 0 + max (-x) 0 := by
    rcases lt_or_ge 0 y with hy | hy
    · have := le_max_left y 0; have := le_max_right (-x) 0; linarith
    · have := le_max_left (-x) 0; have := le_max_right y 0; linarith
  rw [ENNReal.ofReal_lt_ofReal_iff hpos]
  have := max_sub_max x; have := max_sub_max y
  linarith

noncomputable def Fp (S : Model) (ρ : Policy) (ω : ℕ → ℝ) : ENNReal :=
  ∑' k, ENNReal.ofReal (S.α ^ k * S.periodCost ρ ω (k + 1))

noncomputable def Fn (S : Model) (ρ : Policy) (ω : ℕ → ℝ) : ENNReal :=
  ∑' k, ENNReal.ofReal (-(S.α ^ k * S.periodCost ρ ω (k + 1)))

theorem meas_Fp (S : Model) [IsFiniteMeasure S.leadDemandLaw] (ρ : Policy)
    (hρ : MeasurablePolicy ρ) : Measurable (Fp S ρ) :=
  Measurable.ennreal_tsum (fun k =>
    ENNReal.measurable_ofReal.comp ((meas_pc S ρ hρ (k + 1)).const_mul _))

theorem meas_Fn (S : Model) [IsFiniteMeasure S.leadDemandLaw] (ρ : Policy)
    (hρ : MeasurablePolicy ρ) : Measurable (Fn S ρ) :=
  Measurable.ennreal_tsum (fun k =>
    ENNReal.measurable_ofReal.comp ((meas_pc S ρ hρ (k + 1)).const_mul _).neg)

theorem cost_strict (S : Model) [IsFiniteMeasure S.leadDemandLaw] (hα : 0 < S.α)
    (π σ : Policy) (hπ : MeasurablePolicy π) (hσ : MeasurablePolicy σ)
    (hFnπ : ∫⁻ ω, Fn S π ω ∂(Measure.infinitePi fun _ : ℕ => S.ν) < ⊤)
    (hFpπ : ∫⁻ ω, Fp S π ω ∂(Measure.infinitePi fun _ : ℕ => S.ν) < ⊤)
    (hle : ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => S.ν),
      ∀ k, S.periodCost σ ω (k + 1) ≤ S.periodCost π ω (k + 1))
    (hlt : ∃ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => S.ν),
      ∃ k, S.periodCost σ ω (k + 1) < S.periodCost π ω (k + 1)) :
    S.cost σ < S.cost π := by
  set μ := Measure.infinitePi fun _ : ℕ => S.ν
  have hak : ∀ k, 0 ≤ S.α ^ k := fun k => pow_nonneg hα.le k
  have hFpσ : ∫⁻ ω, Fp S σ ω ∂μ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hFpπ
    filter_upwards [hle] with ω hω
    exact ENNReal.tsum_le_tsum (fun k =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hω k) (hak k)))
  set f := fun ω => Fp S σ ω + Fn S π ω with hf
  set g := fun ω => Fp S π ω + Fn S σ ω with hg
  have hmf : Measurable f := (meas_Fp S σ hσ).add (meas_Fn S π hπ)
  have hmg : Measurable g := (meas_Fp S π hπ).add (meas_Fn S σ hσ)
  have hif : ∫⁻ ω, f ω ∂μ = ∫⁻ ω, Fp S σ ω ∂μ + ∫⁻ ω, Fn S π ω ∂μ :=
    lintegral_add_left (meas_Fp S σ hσ) _
  have hig : ∫⁻ ω, g ω ∂μ = ∫⁻ ω, Fp S π ω ∂μ + ∫⁻ ω, Fn S σ ω ∂μ :=
    lintegral_add_left (meas_Fp S π hπ) _
  have hfin : ∫⁻ ω, f ω ∂μ ≠ ⊤ := by
    rw [hif]; exact (ENNReal.add_lt_top.mpr ⟨hFpσ, hFnπ⟩).ne
  have hsplit : ∀ ω, (f ω = ∑' k, (ENNReal.ofReal (S.α ^ k * S.periodCost σ ω (k + 1)) +
      ENNReal.ofReal (-(S.α ^ k * S.periodCost π ω (k + 1))))) ∧
      (g ω = ∑' k, (ENNReal.ofReal (S.α ^ k * S.periodCost π ω (k + 1)) +
      ENNReal.ofReal (-(S.α ^ k * S.periodCost σ ω (k + 1))))) := by
    intro ω
    simp only [hf, hg, Fp, Fn]
    exact ⟨(ENNReal.tsum_add).symm, (ENNReal.tsum_add).symm⟩
  have hfg : f ≤ᵐ[μ] g := by
    filter_upwards [hle] with ω hω
    rw [(hsplit ω).1, (hsplit ω).2]
    exact ENNReal.tsum_le_tsum (fun k =>
      pair_le _ _ (mul_le_mul_of_nonneg_left (hω k) (hak k)))
  have hfae : ∀ᵐ ω ∂μ, f ω < ⊤ := ae_lt_top hmf hfin
  have hne : ∃ᵐ ω ∂μ, f ω ≠ g ω := by
    refine (hlt.and_eventually (hle.and hfae)).mono ?_
    rintro ω ⟨⟨k, hk⟩, hω, hfω⟩
    apply ne_of_lt
    have hfω' := hfω
    rw [(hsplit ω).1] at hfω' ⊢
    rw [(hsplit ω).2]
    exact ENNReal.tsum_lt_tsum hfω'.ne
      (fun k => pair_le _ _ (mul_le_mul_of_nonneg_left (hω k) (hak k)))
      (pair_lt _ _ (mul_lt_mul_of_pos_left hk (pow_pos hα k)))
  have hstrict := lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hmg.aemeasurable hfin hfg hne
  rw [hif, hig] at hstrict
  -- conclude in the extended reals
  unfold Model.cost
  set a := ∫⁻ ω, Fp S σ ω ∂μ
  set b := ∫⁻ ω, Fn S σ ω ∂μ
  set c := ∫⁻ ω, Fp S π ω ∂μ
  set d := ∫⁻ ω, Fn S π ω ∂μ
  show (a : EReal) - (b : EReal) < (c : EReal) - (d : EReal)
  have hcd : (c : EReal) - (d : EReal) = ((c.toReal - d.toReal : ℝ) : EReal) := by
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal hFpπ.ne, EReal.coe_ennreal_toReal hFnπ.ne]
  by_cases hb : b = ⊤
  · rw [hb, EReal.coe_ennreal_top, EReal.sub_top, hcd]
    exact EReal.bot_lt_coe _
  · have hab : (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
      rw [EReal.coe_sub, EReal.coe_ennreal_toReal hFpσ.ne, EReal.coe_ennreal_toReal hb]
    rw [hab, hcd, EReal.coe_lt_coe_iff]
    have := (ENNReal.toReal_lt_toReal (ENNReal.add_lt_top.mpr ⟨hFpσ, hFnπ⟩).ne
      (ENNReal.add_ne_top.mpr ⟨hFpπ.ne, hb⟩)).mpr hstrict
    rw [ENNReal.toReal_add hFpσ.ne hFnπ.ne, ENNReal.toReal_add hFpπ.ne hb] at this
    linarith

/-! ### A feasible policy of finite cost, and lower bounds -/

noncomputable def pol0 (x0 : InitialPositions) : Policy :=
  fun k h b => x0 b 1 - ∑ j : Fin k, h j

theorem Dsum_one (ω : ℕ → ℝ) (τ : ℕ) :
    Dsum ω 1 τ = ∑ j ∈ Finset.range (τ - 1), ω j := by
  unfold Dsum
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _; congr 1; omega

theorem dpol0 (x0 : InitialPositions) (ω : ℕ → ℝ) (b τ : ℕ) :
    decision (pol0 x0) ω b τ = x0 b 1 - Dsum ω 1 τ := by
  unfold decision pol0
  rw [Dsum_one, Fin.sum_univ_eq_sum_range (fun j => ω j)]

theorem pos_pol0 (S : Model) (x0 : InitialPositions) (ω : ℕ → ℝ) (b τ s : ℕ)
    (hτ : 1 ≤ τ) :
    S.pos x0 (pol0 x0) ω b τ s =
      (if s < τ then x0 b 1 else x0 b (s - τ + 1)) - Dsum ω 1 τ := by
  by_cases hs : s < τ
  · rw [pos_sig_of_lt S x0 _ ω b τ s hs, dpol0, if_pos hs]
    have := Finset.sum_Ico_consecutive (fun r => ω (r - 1)) (show 1 ≤ τ - s by omega)
      (show τ - s ≤ τ by omega)
    unfold Dsum; linarith
  · unfold Model.pos Dsum; rw [if_neg hs, if_neg hs]

theorem x0_anti (S : Model) (x0 : InitialPositions) (hInitial : S.WellFormedInitial x0)
    (b : ℕ) (hb : b ∈ Finset.Icc 1 S.N) (s s' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s') :
    x0 b s' ≤ x0 b s := by
  induction s', hss using Nat.le_induction with
  | base => exact le_rfl
  | succ s' hss ih => exact (hInitial.1 b hb s' (by omega)).trans ih

theorem pol0_feasible (S : Model) (x0 : InitialPositions) (hInitial : S.WellFormedInitial x0)
    (ω : ℕ → ℝ) : S.PathFeasible x0 (pol0 x0) ω := by
  intro τ hτ b hb
  constructor
  · rw [pos_pol0 S x0 ω b τ 1 hτ, dpol0]
    by_cases h1 : 1 < τ
    · rw [if_pos h1]
    · rw [if_neg h1]; have : 1 - τ + 1 = 1 := by omega
      rw [this]
  · intro k hk
    have hkI := (Finset.mem_filter.mp hk).1
    rw [pos_pol0 S x0 ω k τ _ hτ, dpol0]
    have h0 := hInitial.2 b hb k hk 1 le_rfl
    split_ifs with hl
    · have := x0_anti S x0 hInitial k hkI 1 (1 + S.lead k) le_rfl (by omega)
      linarith
    · have := x0_anti S x0 hInitial k hkI (S.lead k - τ + 1) (1 + S.lead k) (by omega) (by omega)
      linarith

theorem pol0_meas (x0 : InitialPositions) : MeasurablePolicy (pol0 x0) := by
  intro k b
  exact measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

theorem Ylow (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hF : S.PathFeasible x0 π ω) (b : ℕ) (hb : b ∈ Finset.Icc 1 S.N) :
    ∀ τ ≥ 1, x0 b 1 - Dsum ω 1 τ ≤ decision π ω b τ := by
  intro τ hτ
  induction τ, hτ using Nat.le_induction with
  | base =>
    have := (hF 1 le_rfl b hb).1
    rw [pos_one_one S x0 π ω b 1 le_rfl] at this
    simp [Dsum]; exact this
  | succ τ hτ ih =>
    have h1 := (hF (τ + 1) (by omega) b hb).1
    rw [pos_sig_of_lt S x0 π ω b (τ + 1) 1 (by omega), Nat.add_sub_cancel] at h1
    have := Finset.sum_Ico_consecutive (fun r => ω (r - 1)) hτ (show τ ≤ τ + 1 by omega)
    unfold Dsum at *
    linarith

theorem Dsum_abs (ω : ℕ → ℝ) (k : ℕ) :
    |Dsum ω 1 (k + 1)| ≤ ∑ j ∈ Finset.range k, |ω j| := by
  rw [Dsum_one, Nat.add_sub_cancel]
  exact Finset.abs_sum_le_sum_abs _ _

theorem pH_pos (S : Model) (hTree : S.ValidTree) (hα : 0 < S.α) (hAss : S.Assumption) :
    0 < S.p + S.H1 := by
  refine lt_of_le_of_lt ?_ hAss.2
  apply Finset.sum_nonneg
  intro b hb
  have := hAss.1 b hb
  have : 0 < (S.α ^ S.M (S.succ b))⁻¹ := inv_pos.mpr (pow_pos hα _)
  positivity

theorem Fn_bound (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hTree : S.ValidTree) (hα : 0 < S.α) (hAss : S.Assumption)
    (hF : S.PathFeasible x0 π ω) (k : ℕ) :
    -S.periodCost π ω (k + 1) ≤
      (∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b * |x0 b 1|) +
      (∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b) *
        ∑ j ∈ Finset.range k, |ω j| := by
  unfold Model.periodCost
  have hg := gS_nonneg S (decision π ω 1 (k + 1))
  have hp := pH_pos S hTree hα hAss
  have h3 : 0 ≤ S.α ^ S.lead 1 * (S.p + S.H1) * gS S (decision π ω 1 (k + 1)) := by
    have := pow_pos hα (S.lead 1); positivity
  unfold gS at h3
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  have : -(∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b * decision π ω b (k + 1)) ≤
      ∑ b ∈ Finset.Icc 1 S.N, (S.α ^ S.lead b * S.h b * |x0 b 1| +
        S.α ^ S.lead b * S.h b * ∑ j ∈ Finset.range k, |ω j|) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro b hb
    have hc : 0 ≤ S.α ^ S.lead b * S.h b := by
      have := hAss.1 b hb; have := pow_pos hα (S.lead b); positivity
    have hy := Ylow S x0 π ω hF b hb (k + 1) (by omega)
    have hd := Dsum_abs ω k
    have := neg_abs_le (x0 b 1)
    have := le_abs_self (Dsum ω 1 (k + 1))
    nlinarith
  linarith

theorem Fp0_bound (S : Model) (x0 : InitialPositions) [IsFiniteMeasure S.leadDemandLaw]
    (hTree : S.ValidTree) (hα : 0 < S.α) (hAss : S.Assumption) (ω : ℕ → ℝ) (k : ℕ) :
    S.periodCost (pol0 x0) ω (k + 1) ≤
      ((∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b * |x0 b 1|) +
        S.α ^ S.lead 1 * (S.p + S.H1) *
          (gS S 0 + |x0 1 1| * S.leadDemandLaw.real Set.univ)) +
      ((∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b) +
        S.α ^ S.lead 1 * (S.p + S.H1) * S.leadDemandLaw.real Set.univ) *
        ∑ j ∈ Finset.range k, |ω j| := by
  unfold Model.periodCost
  simp only [dpol0]
  have hp := pH_pos S hTree hα hAss
  have hc1 : 0 ≤ S.α ^ S.lead 1 * (S.p + S.H1) := by
    have := pow_pos hα (S.lead 1); positivity
  have hLr : 0 ≤ S.leadDemandLaw.real Set.univ := measureReal_nonneg
  have hd := Dsum_abs ω k
  have hgb := gS_bound S (x0 1 1 - Dsum ω 1 (k + 1))
  have habs : |x0 1 1 - Dsum ω 1 (k + 1)| ≤ |x0 1 1| + ∑ j ∈ Finset.range k, |ω j| :=
    (abs_sub _ _).trans (add_le_add le_rfl hd)
  have h2 : S.α ^ S.lead 1 * (S.p + S.H1) * gS S (x0 1 1 - Dsum ω 1 (k + 1)) ≤
      S.α ^ S.lead 1 * (S.p + S.H1) *
        (gS S 0 + (|x0 1 1| + ∑ j ∈ Finset.range k, |ω j|) * S.leadDemandLaw.real Set.univ) := by
    apply mul_le_mul_of_nonneg_left _ hc1
    refine hgb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right habs hLr))
  have h1 : (∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b * (x0 b 1 - Dsum ω 1 (k + 1))) ≤
      ∑ b ∈ Finset.Icc 1 S.N, (S.α ^ S.lead b * S.h b * |x0 b 1| +
        S.α ^ S.lead b * S.h b * ∑ j ∈ Finset.range k, |ω j|) := by
    apply Finset.sum_le_sum
    intro b hb
    have hc : 0 ≤ S.α ^ S.lead b * S.h b := by
      have := hAss.1 b hb; have := pow_pos hα (S.lead b); positivity
    have := le_abs_self (x0 b 1)
    have := neg_abs_le (Dsum ω 1 (k + 1))
    nlinarith
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
  have e : (∫ x, max (x - (x0 1 1 - Dsum ω 1 (k + 1))) 0 ∂S.leadDemandLaw) =
      gS S (x0 1 1 - Dsum ω 1 (k + 1)) := rfl
  rw [e]
  linarith

end RoslingAssembly.SeriesEquiv.ReduxAux

open RoslingAssembly.SeriesEquiv RoslingAssembly.SeriesEquiv.ReduxAux MeasureTheory in
theorem solution (S : Model) (x0 : InitialPositions)
    (π : Policy) [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hDemand : S.ValidDemand)
    (hα : 0 < S.α ∧ S.α < 1) (hAssumption : S.Assumption)
    (hInitial : S.WellFormedInitial x0) (hOptimal : S.Optimal x0 π) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν),
      ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
        S.NoExcessAt x0 π ω i t := by
  haveI : IsFiniteMeasure S.leadDemandLaw := by
    unfold Model.leadDemandLaw; infer_instance
  set μ := Measure.infinitePi fun _ : ℕ => S.ν with hμ
  have hπm := hOptimal.1.1
  have hFae := hOptimal.1.2
  have hInt := hDemand.2.2.1
  have hc : ∀ b ∈ Finset.Icc 1 S.N, 0 ≤ S.α ^ S.lead b * S.h b := by
    intro b hb; have := hAssumption.1 b hb; have := pow_pos hα.1 (S.lead b); positivity
  have hA1 : 0 ≤ ∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b * |x0 b 1| :=
    Finset.sum_nonneg (fun b hb => mul_nonneg (hc b hb) (abs_nonneg _))
  have hB1 : 0 ≤ ∑ b ∈ Finset.Icc 1 S.N, S.α ^ S.lead b * S.h b :=
    Finset.sum_nonneg hc
  have hp := pH_pos S hTree hα.1 hAssumption
  have hc1 : 0 ≤ S.α ^ S.lead 1 * (S.p + S.H1) := by
    have := pow_pos hα.1 (S.lead 1); positivity
  have hLr : 0 ≤ S.leadDemandLaw.real Set.univ := measureReal_nonneg
  have hg0 := gS_nonneg S 0
  -- finiteness of the negative part for π
  have hFnπ : ∫⁻ ω, Fn S π ω ∂μ < ⊤ := by
    have := fin_lemma S.ν hInt S.α hα (fun k ω => -S.periodCost π ω (k + 1)) _ _ hA1 hB1
      (hFae.mono (fun ω hω k => Fn_bound S x0 π ω hTree hα.1 hAssumption hω k))
    unfold Fn; simpa [mul_neg] using this
  -- a feasible policy of finite cost
  have hFp0 : ∫⁻ ω, Fp S (pol0 x0) ω ∂μ < ⊤ := by
    have := fin_lemma S.ν hInt S.α hα (fun k ω => S.periodCost (pol0 x0) ω (k + 1)) _ _
      (by positivity) (by positivity)
      (Filter.Eventually.of_forall (fun ω k => Fp0_bound S x0 hTree hα.1 hAssumption ω k))
    exact this
  have hcost0 : S.cost (pol0 x0) < ⊤ := by
    unfold Model.cost
    set b0 := ∫⁻ ω, Fn S (pol0 x0) ω ∂μ
    have ha : ((∫⁻ ω, Fp S (pol0 x0) ω ∂μ : ENNReal) : EReal) =
        (((∫⁻ ω, Fp S (pol0 x0) ω ∂μ).toReal : ℝ) : EReal) :=
      (EReal.coe_ennreal_toReal hFp0.ne).symm
    show ((∫⁻ ω, Fp S (pol0 x0) ω ∂μ : ENNReal) : EReal) - (b0 : EReal) < ⊤
    rw [ha]
    by_cases hb : b0 = ⊤
    · rw [hb, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_lt_top
    · rw [← EReal.coe_ennreal_toReal hb, ← EReal.coe_sub]; exact EReal.coe_lt_top _
  have h0le : S.cost π ≤ S.cost (pol0 x0) :=
    hOptimal.2 _ ⟨pol0_meas x0, Filter.Eventually.of_forall
      (fun ω => pol0_feasible S x0 hInitial ω)⟩
  have hFpπ : ∫⁻ ω, Fp S π ω ∂μ < ⊤ := by
    by_contra hcon
    have htop : ∫⁻ ω, Fp S π ω ∂μ = ⊤ := not_lt_top_iff.mp hcon
    have : S.cost π = ⊤ := by
      unfold Model.cost
      show ((∫⁻ ω, Fp S π ω ∂μ : ENNReal) : EReal) - ((∫⁻ ω, Fn S π ω ∂μ : ENNReal) : EReal) = ⊤
      rw [htop, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hFnπ.ne, EReal.top_sub_coe]
    rw [this] at h0le
    exact absurd (lt_of_le_of_lt h0le hcost0) (lt_irrefl _)
  have key : ∀ t i, ∀ᵐ ω ∂μ,
      (t ≥ 1 → i ∈ Finset.Icc 1 S.N → S.NoExcessAt x0 π ω i t) := by
    intro t i
    by_cases ht : 1 ≤ t
    swap
    · exact Filter.Eventually.of_forall (fun ω h => absurd h ht)
    by_cases hi : i ∈ Finset.Icc 1 S.N
    swap
    · exact Filter.Eventually.of_forall (fun ω _ h => absurd h hi)
    have hi' := Finset.mem_Icc.mp hi
    rcases eq_or_lt_of_le hi'.2 with hiN | hiN
    · exact Filter.Eventually.of_forall (fun ω _ _ => hiN ▸ noExcess_last S x0 π ω t)
    by_contra hcon
    have hfreq : ∃ᵐ ω ∂μ, ¬ S.NoExcessAt x0 π ω i t := by
      rw [Filter.not_eventually] at hcon
      exact hcon.mono (fun ω h h' => h (fun _ _ => h'))
    have hσm := meas_sig S x0 π hπm i t
    have hσF : S.Feasible x0 (sig S x0 π i t) :=
      ⟨hσm, hFae.mono (fun ω hω =>
        sig_feasible S x0 π ω hTree hInitial hω i t hi'.1 hiN ht)⟩
    have hle := hOptimal.2 _ hσF
    have hlt : S.cost (sig S x0 π i t) < S.cost π := by
      apply cost_strict S hα.1 π _ hπm hσm hFnπ hFpπ
      · filter_upwards [hFae] with ω hω k
        exact pc_le S x0 π ω hTree hInitial hω hα.1 hAssumption i t hi'.1 hiN ht (k + 1)
          (by omega)
      · refine (hfreq.and_eventually hFae).mono ?_
        rintro ω ⟨hne, hω⟩
        refine ⟨t - 1, ?_⟩
        rw [Nat.sub_add_cancel ht]
        apply pc_lt S x0 π ω hTree hInitial hω hα.1 hAssumption i t hi'.1 hiN ht
        by_contra hcc
        rw [not_lt] at hcc
        apply hne
        apply noExcess_of_le S x0 π ω i t hiN (hω t ht i hi).1
        exact hcc.trans (by simp only [wv]; exact min_le_right _ _)
    exact absurd hle (not_le.mpr hlt)
  have hall : ∀ᵐ ω ∂μ, ∀ t i,
      (t ≥ 1 → i ∈ Finset.Icc 1 S.N → S.NoExcessAt x0 π ω i t) := by
    rw [ae_all_iff]; intro t; rw [ae_all_iff]; exact key t
  filter_upwards [hall] with ω h t ht i hi
  exact h t i ht hi
