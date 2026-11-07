-- Prove2me | solution 1 for RoslingAssembly.SeriesEquiv.theorem2_equivalent_series
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:56:06.870001+00:00
-- url     : https://prove2.me/submissions/60aa89ff-8b90-43ab-aa9d-a051a5865cf6

import Theorems.Thm_RoslingAssembly_SeriesEquiv_lemma1_no_excess_production
import Theorems.Thm_RoslingAssembly_SeriesEquiv_thm2_cost_rewrite

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

/-- Series feasibility implies assembly feasibility along any path, when the
initial pipeline is in long-run balance. -/
theorem series_to_assembly (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (hTree : S.ValidTree) (hBal : S.InitiallyBalanced x0)
    (h : S.series.PathFeasible x0 π ω) : S.PathFeasible x0 π ω := by
  intro t ht i hi
  have hS := h t ht i hi
  have hi' := Finset.mem_Icc.mp hi
  -- adjacent balance from series feasibility
  have bal : ∀ τ ≥ 1, ∀ j, 1 ≤ j → j < S.N →
      decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1)) := by
    intro τ hτ j hj1 hjN
    have := (h τ hτ j (Finset.mem_Icc.mpr ⟨hj1, hjN.le⟩)).2 (j + 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by
        show j + 1 ≤ S.N; omega⟩, by show j + 1 - 1 = j; omega⟩)
    exact this
  refine ⟨hS.1, ?_⟩
  intro k hk
  obtain ⟨hkI, hks⟩ := Finset.mem_filter.mp hk
  have hkI' := Finset.mem_Icc.mp hkI
  have hk2 : 2 ≤ k := by
    by_contra hc
    have : k = 1 := by omega
    subst this
    rw [hTree.2.1] at hks; omega
  have hik : i < k := by
    have := (hTree.2.2.1 k (Finset.mem_Icc.mpr ⟨hk2, hkI'.2⟩)).2
    omega
  have hstop : S.succStop k = i := by
    unfold Model.succStop; rw [if_neg (by omega)]; exact hks
  have hMk := M_step S hTree k (by omega) hkI'.2
  rw [hstop] at hMk
  have chain : ∀ j, i ≤ j → j ≤ S.N →
      decision π ω i t ≤ S.pos x0 π ω j t (S.M j - S.M i) := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; rw [Nat.sub_self, pos_zero S x0 π ω i t ht]
    | succ j hij ih =>
      intro hj
      have ih' := ih (by omega)
      have hm1 := M_mono S hTree i j hij (by omega)
      have hm2 := M_mono S hTree j (j + 1) (by omega) hj
      have hL : S.L (j + 1) = S.M (j + 1) - S.M j := by
        unfold Model.L; simp
      set a := S.M j - S.M i with ha
      have e : S.M (j + 1) - S.M i = S.L (j + 1) + a := by omega
      refine ih'.trans ?_
      rw [e]
      by_cases hat : a < t
      · have s0 := shift S x0 π ω j t 0 a hat
        rw [zero_add] at s0
        have s1 := shift S x0 π ω (j + 1) t (S.L (j + 1)) a hat
        rw [s0, s1, pos_zero S x0 π ω j (t - a) (by omega)]
        have := bal (t - a) (by omega) j (by omega) (by omega)
        linarith
      · unfold Model.pos
        rw [if_neg hat, if_neg (by omega)]
        have hb := hBal j (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          (S.M i + t - 1) (by omega)
        have e1 : S.M j - (S.M i + t - 1) = a - t + 1 := by omega
        have e2 : S.M (j + 1) - (S.M i + t - 1) = S.L (j + 1) + a - t + 1 := by
          omega
        rw [e1, e2] at hb
        linarith
  have := chain k hik.le hkI'.2
  have e : S.M k - S.M i = S.lead k := by omega
  rw [e] at this
  exact this

/-- Along a path where the assembly constraints and Lemma 1's inequalities
hold, the series constraints hold as well. -/
theorem assembly_lemma1_to_series (S : Model) (x0 : InitialPositions)
    (π : Policy) (ω : ℕ → ℝ) (hTree : S.ValidTree)
    (hInitial : S.WellFormedInitial x0) (hBal : S.InitiallyBalanced x0)
    (hZero : S.ZeroLeadBoundary x0) (hF : S.PathFeasible x0 π ω)
    (hL1 : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N, S.NoExcessAt x0 π ω i t) :
    S.series.PathFeasible x0 π ω := by
  have key : ∀ j, 1 ≤ j → j < S.N → ∀ τ ≥ 1,
      decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1)) := by
    intro j hj1 hjN
    have hmono : ∀ t s, 1 ≤ t →
        S.pos x0 π ω (j + 1) t (s + 1) ≤ S.pos x0 π ω (j + 1) t s := by
      intro t s ht
      apply pos_mono S x0 π ω (j + 1) _ _ t s ht
      · intro τ hτ
        exact (hF τ hτ (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
      · intro s hs
        exact hInitial.1 (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) s hs
    have hL : S.L (j + 1) = S.M (j + 1) - S.M j := by
      unfold Model.L; simp
    have hm2 := M_mono S hTree j (j + 1) (by omega) (by omega)
    have p2 : ∀ τ ≥ 1, S.pos x0 π ω j τ 1 ≤
        S.pos x0 π ω (j + 1) τ (S.L (j + 1) + 1) →
        decision π ω j τ ≤ S.pos x0 π ω (j + 1) τ (S.L (j + 1)) := by
      intro τ hτ hp
      obtain ⟨c1, c2⟩ := hL1 τ hτ j (Finset.mem_Icc.mpr ⟨hj1, hjN.le⟩)
      rcases le_total (S.minLater x0 π ω j τ)
          ((S.pos x0 π ω j τ 1 : ℝ) : WithTop ℝ) with hc | hc
      · rw [c1 hc]
        exact hp.trans (hmono τ _ hτ)
      · have h1 := c2 hc
        have h2 : S.minLater x0 π ω j τ ≤
            ((S.pos x0 π ω (j + 1) τ (S.M (j + 1) - S.M j) : ℝ) : WithTop ℝ) := by
          unfold Model.minLater
          exact Finset.inf_le (f := fun k =>
            ((S.pos x0 π ω k τ (S.M k - S.M j) : ℝ) : WithTop ℝ))
            (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
        rw [← hL] at h2
        exact WithTop.coe_le_coe.mp (h1.trans h2)
    have p1 : ∀ τ ≥ 1, S.pos x0 π ω j τ 1 ≤
        S.pos x0 π ω (j + 1) τ (S.L (j + 1) + 1) := by
      intro τ hτ
      induction τ, hτ using Nat.le_induction with
      | base =>
        rw [pos_one_one S x0 π ω j 1 le_rfl,
          pos_one_one S x0 π ω (j + 1) _ (by omega)]
        by_cases hM : S.M j = 0
        · have := hZero j (Finset.mem_Ico.mpr ⟨hj1, hjN⟩) hM
          rw [hL, hM]; simpa using this
        · have := hBal j (Finset.mem_Ico.mpr ⟨hj1, hjN⟩) (S.M j - 1) (by omega)
          have e1 : S.M j - (S.M j - 1) = 1 := by omega
          have e2 : S.M (j + 1) - (S.M j - 1) = S.L (j + 1) + 1 := by omega
          rw [e1, e2] at this; exact this
      | succ τ hτ ih =>
        have hd := p2 τ hτ ih
        have s0 := shift S x0 π ω j (τ + 1) 0 1 (by omega)
        have s1 := shift S x0 π ω (j + 1) (τ + 1) (S.L (j + 1)) 1 (by omega)
        rw [zero_add] at s0
        rw [s0, s1, Nat.add_sub_cancel, pos_zero S x0 π ω j τ hτ]
        linarith
    intro τ hτ
    exact p2 τ hτ (p1 τ hτ)
  intro t ht i hi
  have hi' := Finset.mem_Icc.mp hi
  refine ⟨(hF t ht i hi).1, ?_⟩
  intro k hk
  obtain ⟨hkI, hks⟩ := Finset.mem_filter.mp hk
  have hkI' : 1 ≤ k ∧ k ≤ S.N := Finset.mem_Icc.mp hkI
  have hks' : k - 1 = i := hks
  have hk : k = i + 1 := by omega
  have hiN : i < S.N := by omega
  subst hk
  exact key i hi'.1 hiN t ht

end RoslingAssembly.SeriesEquiv.ReduxAux

open RoslingAssembly.SeriesEquiv RoslingAssembly.SeriesEquiv.ReduxAux in
theorem solution (S : Model) (x0 : InitialPositions)
    [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hDemand : S.ValidDemand)
    (hα : 0 < S.α ∧ S.α < 1) (hAssumption : S.Assumption)
    (hInitial : S.WellFormedInitial x0)
    (hBalance : S.InitiallyBalanced x0)
    (hZero : S.ZeroLeadBoundary x0) :
    (∀ π : Policy, S.Optimal x0 π → (S.series).Optimal x0 π) ∧
    ((∃ π : Policy, S.Optimal x0 π) →
      ∀ π : Policy, (S.series).Optimal x0 π → S.Optimal x0 π) := by
  have hcost : ∀ σ : Policy, S.cost σ = S.series.cost σ := fun σ =>
    thm2_cost_rewrite S σ hTree hα
  have hSF : ∀ σ : Policy, S.series.Feasible x0 σ → S.Feasible x0 σ := by
    intro σ hσ
    refine ⟨hσ.1, ?_⟩
    have h2 : ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν),
        S.series.PathFeasible x0 σ ω := hσ.2
    exact h2.mono fun ω hω => series_to_assembly S x0 σ ω hTree hBalance hω
  have hOF : ∀ σ : Policy, S.Optimal x0 σ → S.series.Feasible x0 σ := by
    intro σ hσ
    refine ⟨hσ.1.1, ?_⟩
    have hl1 := lemma1_no_excess_production S x0 σ hTree hDemand hα hAssumption
      hInitial hσ
    show ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν),
        S.series.PathFeasible x0 σ ω
    filter_upwards [hl1, hσ.1.2] with ω h1 h2
    exact assembly_lemma1_to_series S x0 σ ω hTree hInitial hBalance hZero h2 h1
  have partA : ∀ π : Policy, S.Optimal x0 π → (S.series).Optimal x0 π := by
    intro π hπ
    refine ⟨hOF π hπ, fun σ hσ => ?_⟩
    rw [← hcost π, ← hcost σ]
    exact hπ.2 σ (hSF σ hσ)
  refine ⟨partA, ?_⟩
  rintro ⟨πs, hπs⟩ π hπ
  refine ⟨hSF π hπ.1, fun σ hσ => ?_⟩
  have h1 : S.series.cost π ≤ S.series.cost πs := hπ.2 πs (hOF πs hπs)
  rw [← hcost π, ← hcost πs] at h1
  exact h1.trans (hπs.2 σ hσ)
