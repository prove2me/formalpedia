-- Prove2me | solution 1 for RoslingAssembly.SeriesEquiv.corollary1_series_bound_keeps_LRB
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:59:54.922888+00:00
-- url     : https://prove2.me/submissions/1955eb10-df91-432a-8f96-89b9f06fe841

import Definitions.Def_RoslingAssembly_SeriesEquiv_Dynamics

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


/-- The generic realization argument behind Theorem 1 and Corollary 1. -/
theorem core (S : Model) (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ)
    (hTree : S.ValidTree) (hInitial : S.WellFormedInitial x0)
    (hDemandNonneg : ∀ k, 0 ≤ ω k)
    (hFeasible : S.PathFeasible x0 π ω)
    (hLemma2 : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N, S.MinProductionAt x0 π ω i t)
    (hQ : ∀ t ≥ 1, ∀ j, 1 ≤ j → j < S.N →
      decision π ω j t ≤ S.pos x0 π ω (j + 1) t (S.L (j + 1)) ∨
      (decision π ω j t = S.pos x0 π ω j t 1 ∧
        ∃ k ∈ Finset.Ioc j S.N,
          S.pos x0 π ω k t (S.M k - S.M j) < S.pos x0 π ω j t 1)) :
    (∀ t ≥ 1, S.LongRunBalance x0 π ω t →
      S.LongRunBalance x0 π ω (t + 1)) ∧
    (∀ s : ℕ, (∀ i ∈ Finset.Icc 1 S.N, x0 i 1 < ∑ r ∈ Finset.range s, ω r) →
      ∀ t ≥ s + S.M S.N + 1, S.LongRunBalance x0 π ω t) := by
  have hmono : ∀ x, 1 ≤ x → x ≤ S.N → ∀ t s, 1 ≤ t →
      S.pos x0 π ω x t (s + 1) ≤ S.pos x0 π ω x t s := by
    intro x hx1 hxN t s ht
    apply pos_mono S x0 π ω x _ _ t s ht
    · intro τ hτ
      exact (hFeasible τ hτ x (Finset.mem_Icc.mpr ⟨hx1, hxN⟩)).1
    · intro s hs
      exact hInitial.1 x (Finset.mem_Icc.mpr ⟨hx1, hxN⟩) s hs
  have hL : ∀ j, S.L (j + 1) = S.M (j + 1) - S.M j := by
    intro j; unfold Model.L; simp
  -- persistence of adjacent balance
  have persist : ∀ j, 1 ≤ j → j < S.N → ∀ τ ≥ 1,
      decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1)) →
      decision π ω j (τ + 1) ≤ S.pos x0 π ω (j + 1) (τ + 1) (S.L (j + 1)) := by
    intro j hj1 hjN τ hτ hb
    rcases hQ (τ + 1) (by omega) j hj1 hjN with h | ⟨h, _⟩
    · exact h
    · rw [h]
      have s0 := shift S x0 π ω j (τ + 1) 0 1 (by omega)
      have s1 := shift S x0 π ω (j + 1) (τ + 1) (S.L (j + 1)) 1 (by omega)
      rw [zero_add] at s0
      rw [s0, Nat.add_sub_cancel, pos_zero S x0 π ω j τ hτ]
      have hm := hmono (j + 1) (by omega) (by omega) (τ + 1) (S.L (j + 1)) (by omega)
      rw [s1, Nat.add_sub_cancel] at hm
      linarith
  refine ⟨?_, ?_⟩
  · intro t ht hLRB i hi μ hμ
    have hi' := Finset.mem_Ico.mp hi
    have hm2 := M_mono S hTree i (i + 1) (by omega) (by omega)
    have e1 : S.M i - μ = (S.M i - (μ + 1)) + 1 := by omega
    have e2 : S.M (i + 1) - μ = (S.M (i + 1) - (μ + 1)) + 1 := by omega
    rw [e1, e2, shift S x0 π ω i (t + 1) _ 1 (by omega),
      shift S x0 π ω (i + 1) (t + 1) _ 1 (by omega), Nat.add_sub_cancel]
    suffices S.pos x0 π ω i t (S.M i - (μ + 1)) ≤
        S.pos x0 π ω (i + 1) t (S.M (i + 1) - (μ + 1)) by linarith
    by_cases hμ1 : μ + 1 < S.M i
    · exact hLRB i hi (μ + 1) hμ1
    · have hμe : μ + 1 = S.M i := by omega
      rw [hμe, Nat.sub_self, pos_zero S x0 π ω i t ht, ← hL i]
      rcases hQ t ht i hi'.1 hi'.2 with h | ⟨h, _⟩
      · exact h
      · rw [h]
        have hb := hLRB i hi (S.M i - 1) (by omega)
        have e3 : S.M i - (S.M i - 1) = 1 := by omega
        have e4 : S.M (i + 1) - (S.M i - 1) = S.L (i + 1) + 1 := by
          rw [hL]; omega
        rw [e3, e4] at hb
        exact hb.trans (hmono (i + 1) (by omega) (by omega) t _ ht)
  · intro s hs t ht
    set D : ℕ → ℕ → ℝ := fun a b => ∑ r ∈ Finset.Ico a b, ω (r - 1) with hD
    have Dnn : ∀ a b, 0 ≤ D a b := fun a b =>
      Finset.sum_nonneg (fun r _ => hDemandNonneg _)
    have Dsplit : ∀ a b c, a ≤ b → b ≤ c → D a b + D b c = D a c := by
      intro a b c hab hbc
      exact Finset.sum_Ico_consecutive _ hab hbc
    -- lower bound on production after time s
    have lowerY : ∀ n, ∀ k, 1 ≤ k → k ≤ S.N → S.N - k ≤ n →
        ∀ τ ≥ s + 1 + (S.M S.N - S.M k), -D (s + 1) τ ≤ decision π ω k τ := by
      intro n
      induction n with
      | zero =>
        intro k hk1 hkN hn τ hτ
        have hkeq : k = S.N := by omega
        have h2 := hLemma2 τ (by omega) k (Finset.mem_Icc.mpr ⟨hk1, hkN⟩)
        unfold Model.MinProductionAt Model.minLater at h2
        rw [hkeq, Finset.Ioc_self, Finset.inf_empty] at h2
        simp only [min_eq_left le_top] at h2
        have := WithTop.coe_le_coe.mp h2
        rw [hkeq]
        linarith [Dnn (s + 1) τ]
      | succ n ih =>
        intro k hk1 hkN hn τ hτ
        have h2 := hLemma2 τ (by omega) k (Finset.mem_Icc.mpr ⟨hk1, hkN⟩)
        unfold Model.MinProductionAt at h2
        have hlow : (((-D (s + 1) τ) : ℝ) : WithTop ℝ) ≤
            min (0 : WithTop ℝ) (S.minLater x0 π ω k τ) := by
          apply le_min
          · exact WithTop.coe_le_coe.mpr (by linarith [Dnn (s + 1) τ])
          · unfold Model.minLater
            apply Finset.le_inf
            intro j hj
            have hj' := Finset.mem_Ioc.mp hj
            have hmj := M_mono S hTree k j hj'.1.le hj'.2
            have hmN := M_mono S hTree j S.N hj'.2 le_rfl
            set a := S.M j - S.M k
            have sh := shift S x0 π ω j τ 0 a (by omega)
            rw [zero_add] at sh
            apply WithTop.coe_le_coe.mpr
            rw [sh, pos_zero S x0 π ω j (τ - a) (by omega)]
            have := ih j (by omega) hj'.2 (by omega) (τ - a) (by omega)
            have := Dsplit (s + 1) (τ - a) τ (by omega) (by omega)
            simp only [hD] at *
            linarith
        exact WithTop.coe_le_coe.mp (hlow.trans h2)
    have lowerX : ∀ i k, 1 ≤ i → i < k → k ≤ S.N →
        ∀ τ ≥ s + 1 + (S.M S.N - S.M i),
        -D (s + 1) τ ≤ S.pos x0 π ω k τ (S.M k - S.M i) := by
      intro i k hi hik hkN τ hτ
      have hmj := M_mono S hTree i k hik.le hkN
      have hmN := M_mono S hTree k S.N hkN le_rfl
      set a := S.M k - S.M i
      have sh := shift S x0 π ω k τ 0 a (by omega)
      rw [zero_add] at sh
      rw [sh, pos_zero S x0 π ω k (τ - a) (by omega)]
      have := lowerY (S.N - k) k (by omega) hkN le_rfl (τ - a) (by omega)
      have := Dsplit (s + 1) (τ - a) τ (by omega) (by omega)
      simp only [hD] at *
      linarith
    -- failure of balance forces no ordering so far
    have noorder : ∀ j, 1 ≤ j → j < S.N → ∀ τ ≥ 1,
        ¬ (decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1))) →
        S.pos x0 π ω j τ 1 = x0 j 1 - D 1 τ := by
      intro j hj1 hjN τ hτ
      induction τ, hτ using Nat.le_induction with
      | base =>
        intro _
        rw [pos_one_one S x0 π ω j 1 le_rfl]
        simp [hD]
      | succ τ hτ ih =>
        intro hnb
        have hnb' : ¬ (decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1))) :=
          fun h => hnb (persist j hj1 hjN τ hτ h)
        have hX := ih hnb'
        have hY : decision π ω j τ = S.pos x0 π ω j τ 1 := by
          rcases hQ τ hτ j hj1 hjN with h | ⟨h, _⟩
          · exact absurd h hnb'
          · exact h
        have s0 := shift S x0 π ω j (τ + 1) 0 1 (by omega)
        rw [zero_add] at s0
        rw [s0, Nat.add_sub_cancel, pos_zero S x0 π ω j τ hτ, hY, hX]
        have := Dsplit 1 τ (τ + 1) hτ (by omega)
        have h1 : D τ (τ + 1) = ∑ r ∈ Finset.Ico τ (τ + 1), ω (r - 1) := rfl
        simp only [hD] at *
        linarith
    have balLate : ∀ j, 1 ≤ j → j < S.N → ∀ τ ≥ s + 1 + (S.M S.N - S.M j),
        decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1)) := by
      intro j hj1 hjN τ hτ
      by_contra hnb
      have hX := noorder j hj1 hjN τ (by omega) hnb
      rcases hQ τ (by omega) j hj1 hjN with h | ⟨_, k, hk, hlt⟩
      · exact hnb h
      · have hk' := Finset.mem_Ioc.mp hk
        have hlo := lowerX j k hj1 hk'.1 hk'.2 τ hτ
        have hx0 := hs j (Finset.mem_Icc.mpr ⟨hj1, hjN.le⟩)
        have hsum : D 1 (s + 1) = ∑ r ∈ Finset.range s, ω r := by
          simp only [hD]
          rw [Finset.sum_Ico_eq_sum_range]
          apply Finset.sum_congr (by simp)
          intro r _; congr 1; omega
        have := Dsplit 1 (s + 1) τ (by omega) (by omega)
        rw [hX] at hlt
        linarith
    intro i hi μ hμ
    have hi' := Finset.mem_Ico.mp hi
    have hm2 := M_mono S hTree i (i + 1) (by omega) (by omega)
    have hmN := M_mono S hTree i S.N (by omega) le_rfl
    have hmN' := M_mono S hTree (i + 1) S.N (by omega) le_rfl
    set a := S.M i - μ
    have e2 : S.M (i + 1) - μ = S.L (i + 1) + a := by rw [hL]; omega
    have s0 := shift S x0 π ω i t 0 a (by omega)
    rw [zero_add] at s0
    rw [e2, s0, shift S x0 π ω (i + 1) t (S.L (i + 1)) a (by omega),
      pos_zero S x0 π ω i (t - a) (by omega)]
    have := balLate i hi'.1 hi'.2 (t - a) (by omega)
    linarith

end RoslingAssembly.SeriesEquiv.ReduxAux

open RoslingAssembly.SeriesEquiv RoslingAssembly.SeriesEquiv.ReduxAux in
theorem solution (S : Model) (x0 : InitialPositions)
    (π : Policy) (ω : ℕ → ℝ) (hTree : S.ValidTree)
    (hInitial : S.WellFormedInitial x0)
    (hDemandNonneg : ∀ k, 0 ≤ ω k)
    (hFeasible : S.PathFeasible x0 π ω)
    (hSeriesBound : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
      S.SeriesNoExcessAt x0 π ω i t)
    (hLemma2 : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
      S.MinProductionAt x0 π ω i t) :
    (∀ t ≥ 1, S.LongRunBalance x0 π ω t →
      S.LongRunBalance x0 π ω (t + 1)) ∧
    (∀ s : ℕ, (∑ r ∈ Finset.range s, ω r) >
      (Finset.Icc 1 S.N).sup' (by
        have hn : 1 ∈ Finset.Icc 1 S.N := Finset.mem_Icc.mpr ⟨le_refl 1, hTree.1⟩
        exact Finset.nonempty_iff_ne_empty.mpr (Finset.ne_empty_of_mem hn))
        (fun i => x0 i 1) →
      ∀ t ≥ s + S.M S.N + 1, S.LongRunBalance x0 π ω t) := by
  have hQ : ∀ t ≥ 1, ∀ j, 1 ≤ j → j < S.N →
      decision π ω j t ≤ S.pos x0 π ω (j + 1) t (S.L (j + 1)) ∨
      (decision π ω j t = S.pos x0 π ω j t 1 ∧
        ∃ k ∈ Finset.Ioc j S.N,
          S.pos x0 π ω k t (S.M k - S.M j) < S.pos x0 π ω j t 1) := by
    intro t ht j hj1 hjN
    obtain ⟨c1, c2⟩ := hSeriesBound t ht j (Finset.mem_Icc.mpr ⟨hj1, hjN.le⟩) hjN
    have hL : S.L (j + 1) = S.M (j + 1) - S.M j := by
      unfold Model.L; simp
    rcases le_or_gt (S.pos x0 π ω j t 1) (S.pos x0 π ω (j + 1) t (S.L (j + 1)))
      with hc | hc
    · left; exact c2 hc
    · right
      refine ⟨c1 hc.le, j + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [← hL]; exact hc
  obtain ⟨c1, c2⟩ := core S x0 π ω hTree hInitial hDemandNonneg hFeasible hLemma2 hQ
  refine ⟨c1, fun s hs => c2 s (fun i hi => lt_of_le_of_lt ?_ hs)⟩
  exact Finset.le_sup' (fun i => x0 i 1) hi
