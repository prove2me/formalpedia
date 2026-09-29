-- Prove2me | solution 1 for Rudin.ch02_heine_borel
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-12T22:13:58.658895+00:00
-- url     : https://prove2.me/submissions/07a14ef8-f0b7-4273-92fa-111d49d656ba

import Mathlib
import Definitions.Def_Rudin_ch02_topology

/-!
# Rudin, Theorem 2.41 — Heine–Borel in `ℝ^k`

For `E ⊆ ℝ^k` the following are equivalent: `E` is closed and bounded; `E` is compact;
every infinite subset of `E` has a limit point in `E`.
-/

namespace Rudin

variable {X : Type*} [MetricSpace X]

/-- Rudin's limit points (Definition 2.18(b)) are exactly Mathlib's accumulation points. -/
theorem isLimitPoint_iff_accPt {p : X} {S : Set X} :
    IsLimitPoint p S ↔ AccPt p (Filter.principal S) := by
  constructor
  · intro h
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨q, hqS, hqp, hqd⟩ := h r hr
    exact ⟨q, ⟨hball (Metric.mem_ball.2 hqd), hqS⟩, hqp⟩
  · intro h r hr
    obtain ⟨q, ⟨hqU, hqS⟩, hqp⟩ := accPt_iff_nhds.1 h (Metric.ball p r) (Metric.ball_mem_nhds p hr)
    exact ⟨q, hqS, hqp, Metric.mem_ball.1 hqU⟩

/-- Every ball around a limit point of `S` contains infinitely many points of `S`. -/
theorem IsLimitPoint.infinite_inter_ball {p : X} {S : Set X} (h : IsLimitPoint p S)
    {r : ℝ} (hr : 0 < r) : (S ∩ Metric.ball p r).Infinite := by
  have hacc : AccPt p (Filter.principal S) := isLimitPoint_iff_accPt.1 h
  refine Set.Infinite.of_accPt (x := p) ?_
  have hle : (nhdsWithin p {p}ᶜ ⊓ Filter.principal S) ≤ Filter.principal (Metric.ball p r) :=
    le_trans inf_le_left (le_trans nhdsWithin_le_nhds
      (Filter.le_principal_iff.2 (Metric.ball_mem_nhds p hr)))
  have heq : nhdsWithin p {p}ᶜ ⊓ Filter.principal (S ∩ Metric.ball p r)
      = nhdsWithin p {p}ᶜ ⊓ Filter.principal S := by
    rw [← Filter.inf_principal, ← inf_assoc, inf_eq_left.2 hle]
  show (nhdsWithin p {p}ᶜ ⊓ Filter.principal (S ∩ Metric.ball p r)).NeBot
  rw [heq]
  exact hacc

end Rudin

open Rudin in
theorem solution (k : ℕ) (E : Set (EuclideanSpace ℝ (Fin k))) :
    [IsClosed E ∧ Bornology.IsBounded E,
      IsCompact E,
      ∀ S ⊆ E, S.Infinite → ∃ p ∈ E, IsLimitPoint p S].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    exact Metric.isCompact_iff_isClosed_bounded.2 ⟨h.1, h.2⟩
  tfae_have 2 → 3 := by
    intro hE S hSE hS
    obtain ⟨p, hpE, hp⟩ := hS.exists_accPt_of_subset_isCompact hE hSE
    exact ⟨p, hpE, isLimitPoint_iff_accPt.2 hp⟩
  tfae_have 3 → 1 := by
    intro h
    constructor
    · -- `E` is closed
      rw [← closure_subset_iff_isClosed]
      intro p hp
      by_contra hpE
      have hx : ∀ n : ℕ, ∃ y ∈ E, dist y p < 1 / (n + 1) := by
        intro n
        have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
        obtain ⟨y, hyE, hy⟩ := Metric.mem_closure_iff.1 hp _ hpos
        exact ⟨y, hyE, by rwa [dist_comm] at hy⟩
      choose x hxE hxd using hx
      have hSE : Set.range x ⊆ E := by rintro _ ⟨n, rfl⟩; exact hxE n
      have hSinf : (Set.range x).Infinite := by
        intro hfin
        have hpS : p ∉ Set.range x := fun hps => hpE (hSE hps)
        obtain ⟨ε, hε, hball⟩ :=
          Metric.isOpen_iff.1 hfin.isClosed.isOpen_compl p hpS
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
        have hn1 : (1:ℝ) / (n + 1) < ε := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hn
          nlinarith
        exact hball (Metric.mem_ball.2 ((hxd n).trans hn1)) ⟨n, rfl⟩
      obtain ⟨q, hqE, hq⟩ := h (Set.range x) hSE hSinf
      have hqp : q ≠ p := fun heq => hpE (heq ▸ hqE)
      have hd : 0 < dist q p := dist_pos.2 hqp
      refine hq.infinite_inter_ball (r := dist q p / 2) (by positivity) ?_
      refine Set.Finite.subset
        (Set.Finite.image x (Set.finite_Iio ⌈2 / dist q p⌉₊)) ?_
      rintro y ⟨⟨n, rfl⟩, hyb⟩
      refine ⟨n, ?_, rfl⟩
      have htri : dist q p ≤ dist q (x n) + dist (x n) p := dist_triangle q (x n) p
      have hqx : dist q (x n) < dist q p / 2 := by
        rw [dist_comm]; exact Metric.mem_ball.1 hyb
      have hlow : dist q p / 2 < dist (x n) p := by linarith
      have hlt : dist q p / 2 < 1 / ((n : ℝ) + 1) := hlow.trans (hxd n)
      have ht : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have h3 : dist q p * ((n : ℝ) + 1) < 1 * 2 := (div_lt_div_iff₀ two_pos ht).1 hlt
      rw [Set.mem_Iio, Nat.lt_ceil, lt_div_iff₀ hd]
      nlinarith
    · -- `E` is bounded
      by_contra hb
      have hx : ∀ n : ℕ, ∃ y ∈ E, (n : ℝ) < ‖y‖ := by
        intro n
        by_contra hcon
        exact hb (isBounded_iff_forall_norm_le.2
          ⟨n, fun y hy => not_lt.1 fun hlt => hcon ⟨y, hy, hlt⟩⟩)
      choose x hxE hxn using hx
      have hSE : Set.range x ⊆ E := by rintro _ ⟨n, rfl⟩; exact hxE n
      have hSinf : (Set.range x).Infinite := by
        intro hfin
        obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hfin.isBounded
        obtain ⟨n, hn⟩ := exists_nat_gt C
        exact absurd (hC _ ⟨n, rfl⟩) (by nlinarith [hxn n])
      obtain ⟨p, hpE, hp⟩ := h (Set.range x) hSE hSinf
      refine hp.infinite_inter_ball (r := 1) one_pos ?_
      refine Set.Finite.subset (Set.Finite.image x (Set.finite_Iio ⌈‖p‖ + 1⌉₊)) ?_
      rintro y ⟨⟨n, rfl⟩, hyb⟩
      refine ⟨n, ?_, rfl⟩
      have hball : dist (x n) p < 1 := Metric.mem_ball.1 hyb
      have hnorm : ‖x n‖ - ‖p‖ ≤ dist (x n) p := by
        rw [dist_eq_norm]; exact norm_sub_norm_le _ _
      rw [Set.mem_Iio, Nat.lt_ceil]
      nlinarith [hxn n]
  tfae_finish
