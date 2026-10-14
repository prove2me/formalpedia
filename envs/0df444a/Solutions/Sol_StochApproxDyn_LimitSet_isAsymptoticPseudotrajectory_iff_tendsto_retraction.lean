-- Prove2me | solution 1 for StochApproxDyn.LimitSet.isAsymptoticPseudotrajectory_iff_tendsto_retraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:38:50.277555+00:00
-- url     : https://prove2.me/submissions/d1576016-e2d8-467f-b159-6fd34577db7a

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow

open scoped NNReal


namespace StochApproxDyn.LimitSet

theorem d45r_sup_eq {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (k : ℕ)
    (t : ℝ≥0) :
    supDistOn k (translate t X) (retraction Φ (translate t X)) =
      ⨆ s : Set.Icc (0 : ℝ≥0) (k : ℝ≥0), dist (X (t + s)) (Φ s (X t)) := by
  unfold supDistOn
  congr 1
  ext s
  simp [translate, retraction, trajectory]

theorem d45r_bdd {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (k : ℕ)
    (t : ℝ≥0) :
    BddAbove (Set.range fun s : Set.Icc (0 : ℝ≥0) (k : ℝ≥0) => dist (X (t + s)) (Φ s (X t))) := by
  have hc : Continuous fun s : Set.Icc (0 : ℝ≥0) (k : ℝ≥0) => dist (X (t + s)) (Φ s (X t)) := by
    apply Continuous.dist
    · exact X.continuous.comp (continuous_const.add continuous_subtype_val)
    · exact Φ.continuous continuous_subtype_val continuous_const
  haveI : CompactSpace (Set.Icc (0 : ℝ≥0) (k : ℝ≥0)) := isCompact_iff_compactSpace.mp isCompact_Icc
  exact (isCompact_range hc).bddAbove

theorem d45r_le_sup {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (k : ℕ)
    (t s : ℝ≥0) (hs : s ≤ k) :
    dist (X (t + s)) (Φ s (X t)) ≤
      supDistOn k (translate t X) (retraction Φ (translate t X)) := by
  rw [d45r_sup_eq]
  exact le_ciSup (f := fun s : Set.Icc (0 : ℝ≥0) (k : ℝ≥0) => dist (X (t + s)) (Φ s (X t)))
    (d45r_bdd Φ X k t) ⟨s, zero_le, hs⟩

theorem d45r_sup_le {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (k : ℕ)
    (t : ℝ≥0) (ε : ℝ) (h : ∀ s : ℝ≥0, s ≤ k → dist (X (t + s)) (Φ s (X t)) ≤ ε) :
    supDistOn k (translate t X) (retraction Φ (translate t X)) ≤ ε := by
  rw [d45r_sup_eq]
  haveI : Nonempty (Set.Icc (0 : ℝ≥0) (k : ℝ≥0)) := ⟨⟨0, le_rfl, zero_le⟩⟩
  exact ciSup_le fun s => h s s.2.2

theorem d45r_sup_nonneg {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) (k : ℕ)
    (t : ℝ≥0) : 0 ≤ supDistOn k (translate t X) (retraction Φ (translate t X)) :=
  le_trans dist_nonneg (d45r_le_sup Φ X k t 0 zero_le)

theorem d45r_term_nonneg {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M))
    (t : ℝ≥0) (k : ℕ) :
    0 ≤ (1 / 2 : ℝ) ^ k * min 1 (supDistOn k (translate t X) (retraction Φ (translate t X))) :=
  mul_nonneg (by positivity) (le_min zero_le_one (d45r_sup_nonneg Φ X k t))

theorem d45r_summable {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M))
    (t : ℝ≥0) :
    Summable fun k : ℕ =>
      (1 / 2 : ℝ) ^ k * min 1 (supDistOn k (translate t X) (retraction Φ (translate t X))) := by
  refine Summable.of_nonneg_of_le (d45r_term_nonneg Φ X t) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2 : ℝ) < 1))
  calc (1 / 2 : ℝ) ^ k * min 1 (supDistOn k (translate t X) (retraction Φ (translate t X)))
      ≤ (1 / 2 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ = (1 / 2 : ℝ) ^ k := mul_one _

theorem d45r_core {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) :
    IsAsymptoticPseudotrajectory Φ X ↔
      Filter.Tendsto
        (fun t : ℝ≥0 => uniformCompactDist (translate t X) (retraction Φ (translate t X)))
        Filter.atTop (nhds 0) := by
  constructor
  · rintro ⟨_, hapt⟩
    unfold uniformCompactDist
    have hsum0 : (∑' _k : ℕ, (0 : ℝ)) = 0 := tsum_zero
    rw [← hsum0]
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun k : ℕ => (1 / 2 : ℝ) ^ k)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2 : ℝ) < 1))
    · intro k
      have hd : Filter.Tendsto
          (fun t : ℝ≥0 => supDistOn k (translate t X) (retraction Φ (translate t X)))
          Filter.atTop (nhds 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨t₀, ht₀⟩ := hapt ((k : ℝ≥0) + 1) (by positivity) (ε / 2) (by linarith)
        refine ⟨t₀, fun t ht => ?_⟩
        have h1 := d45r_sup_le Φ X k t (ε / 2) (fun s hs =>
          (ht₀ t ht s (le_trans hs le_self_add)).le)
        have h2 := d45r_sup_nonneg Φ X k t
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
        linarith
      have h3 : Filter.Tendsto
          (fun t : ℝ≥0 => (1 / 2 : ℝ) ^ k *
            min 1 (supDistOn k (translate t X) (retraction Φ (translate t X))))
          Filter.atTop (nhds ((1 / 2 : ℝ) ^ k * min 1 0)) :=
        ((tendsto_const_nhds (x := (1:ℝ))).min hd).const_mul _
      simpa using h3
    · refine Filter.Eventually.of_forall fun t k => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (d45r_term_nonneg Φ X t k)]
      calc (1 / 2 : ℝ) ^ k * min 1 (supDistOn k (translate t X) (retraction Φ (translate t X)))
          ≤ (1 / 2 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
        _ = (1 / 2 : ℝ) ^ k := mul_one _
  · intro h
    refine ⟨X.continuous, fun T _ ε hε => ?_⟩
    set k := Nat.ceil T with hk
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k * min 1 ε := mul_pos (by positivity) (lt_min one_pos hε)
    obtain ⟨t₀, ht₀⟩ := Metric.tendsto_atTop.mp h _ hpos
    refine ⟨t₀, fun t ht s hs => ?_⟩
    have h1 := ht₀ t ht
    have hnn : 0 ≤ uniformCompactDist (translate t X) (retraction Φ (translate t X)) :=
      tsum_nonneg (d45r_term_nonneg Φ X t)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h1
    have h2 := (d45r_summable Φ X t).le_tsum k (fun j _ => d45r_term_nonneg Φ X t j)
    have h3 : (1 / 2 : ℝ) ^ k *
        min 1 (supDistOn k (translate t X) (retraction Φ (translate t X))) <
        (1 / 2 : ℝ) ^ k * min 1 ε := lt_of_le_of_lt h2 h1
    have h4 : min 1 (supDistOn k (translate t X) (retraction Φ (translate t X))) < min 1 ε :=
      lt_of_mul_lt_mul_left h3 (by positivity)
    have h5 : supDistOn k (translate t X) (retraction Φ (translate t X)) < ε := by
      by_contra hc
      push_neg at hc
      exact absurd h4 (not_lt.mpr (min_le_min le_rfl hc))
    have hsk : s ≤ (k : ℝ≥0) := le_trans hs (Nat.le_ceil T)
    exact lt_of_le_of_lt (d45r_le_sup Φ X k t s hsk) h5

end StochApproxDyn.LimitSet

open StochApproxDyn.LimitSet


theorem solution {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) :
    IsAsymptoticPseudotrajectory Φ X ↔
      Filter.Tendsto
        (fun t : ℝ≥0 => uniformCompactDist (translate t X) (retraction Φ (translate t X)))
        Filter.atTop (nhds 0) := by
  exact d45r_core Φ X
