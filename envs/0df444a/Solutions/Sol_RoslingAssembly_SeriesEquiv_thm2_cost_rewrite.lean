-- Prove2me | solution 1 for RoslingAssembly.SeriesEquiv.thm2_cost_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:50:24.921589+00:00
-- url     : https://prove2.me/submissions/8aac837c-e460-4794-9ded-6a52f445b33f

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv.CostAux
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

end RoslingAssembly.SeriesEquiv.CostAux

open RoslingAssembly.SeriesEquiv RoslingAssembly.SeriesEquiv.CostAux in
theorem solution (S : Model) (π : Policy)
    [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hα : 0 < S.α ∧ S.α < 1) :
    S.cost π = (S.series).cost π := by
  have hL1 := L_one S hTree
  have hlaw : S.series.leadDemandLaw = S.leadDemandLaw := by
    unfold Model.leadDemandLaw
    show (MeasureTheory.Measure.pi (fun _ : Fin (S.L 1 + 1) => S.ν)).map
        (fun z => ∑ j, z j) = _
    rw [hL1]
  have hpc : ∀ ω t, S.series.periodCost π ω t = S.periodCost π ω t := by
    intro ω t
    unfold Model.periodCost
    rw [hlaw]
    show (∑ i ∈ Finset.Icc 1 S.N,
        S.α ^ S.L i * (S.h i * S.α ^ (S.lead i - S.L i)) * decision π ω i t) +
      S.α ^ S.L 1 * (S.p + S.H1) *
        ∫ x, max (x - decision π ω 1 t) 0 ∂S.leadDemandLaw = _
    rw [hL1]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hle := L_le_lead S hTree i hi.1 hi.2
    have : S.α ^ S.L i * (S.h i * S.α ^ (S.lead i - S.L i)) =
        S.α ^ S.lead i * S.h i := by
      rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hle, mul_comm]
    rw [this]
  unfold Model.cost
  simp only [hpc]
  rfl
