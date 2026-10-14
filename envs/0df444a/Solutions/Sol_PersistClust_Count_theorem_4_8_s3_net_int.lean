-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_s3_net_int
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T15:26:03.502118+00:00
-- url     : https://prove2.me/submissions/de775c18-ae09-4f9a-8598-5e603f603b96

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

open PersistClust.Count

theorem miss_le_expBound (n : ℕ) (a : ℝ) (V t : ℝ≥0∞) (ha : 0 ≤ a)
    (hW : ENNReal.ofReal a * V ≤ t) (ht : t ≤ 1) :
    (1 - t) ^ n ≤ expBound (n * a) V := by
  by_cases hWtop : ENNReal.ofReal a * V = ⊤
  · have hinfty : (⊤ : ℝ≥0∞) ≤ t := by rw [← hWtop]; exact hW
    exact absurd (le_trans hinfty ht) (by simp)
  · have hW1 : ENNReal.ofReal a * V ≤ 1 := le_trans hW ht
    have hsub : 1 - t ≤ 1 - ENNReal.ofReal a * V := tsub_le_tsub_left hW 1
    -- `W := ofReal a * V ≠ ∞`, so `W = ofReal w` with `w := W.toReal`
    have hw0 : 0 ≤ (ENNReal.ofReal a * V).toReal := ENNReal.toReal_nonneg
    have hw1 : (ENNReal.ofReal a * V).toReal ≤ 1 := by
      have h' := (ENNReal.toReal_le_toReal hWtop (by simp)).mpr hW1
      rwa [ENNReal.toReal_one] at h'
    have hWval : ENNReal.ofReal ((ENNReal.ofReal a * V).toReal) = ENNReal.ofReal a * V :=
      ENNReal.ofReal_toReal hWtop
    -- `1 − W = ofReal (1 − w)`
    have h1W : 1 - ENNReal.ofReal a * V
        = ENNReal.ofReal (1 - (ENNReal.ofReal a * V).toReal) := by
      rw [ENNReal.ofReal_sub 1 hw0, ENNReal.ofReal_one, hWval]
    -- pow mono by induction (no OrderedCommMonoid pow lemma needed)
    have hpm : ∀ m : ℕ, (1 - t) ^ m ≤ (1 - ENNReal.ofReal a * V) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ]; exact mul_le_mul' ih hsub
    -- cast bridge: `ofReal (↑n * a) * V = ↑n * (ofReal a * V)`
    have hbr : ENNReal.ofReal ((n : ℝ) * a) * V
        = (n : ℝ≥0∞) * (ENNReal.ofReal a * V) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, mul_assoc]
    have hne : ENNReal.ofReal ((n : ℝ) * a) * V ≠ ⊤ := by
      rw [hbr]; exact ENNReal.mul_ne_top (by simp) hWtop
    -- so `expBound (n * a) V` sits in its `else` branch
    have hex : expBound (n * a) V
        = ENNReal.ofReal (Real.exp (-(ENNReal.ofReal ((n : ℝ) * a) * V).toReal)) := by
      simp only [expBound]
      split
      · next h => exact absurd h hne
      · rfl
    -- toReal bridge: `(ofReal (↑n * a) * V).toReal = ↑n * w`
    have htr : (ENNReal.ofReal ((n : ℝ) * a) * V).toReal
        = (n : ℝ) * (ENNReal.ofReal a * V).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) ha),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
      ring
    -- the ℝ chain: `(1 − w) ^ n ≤ e ^ (−(n * w))`
    have h1w : 1 - (ENNReal.ofReal a * V).toReal
        ≤ Real.exp (-(ENNReal.ofReal a * V).toReal) := by
      have h2 := Real.add_one_le_exp (-(ENNReal.ofReal a * V).toReal)
      linarith
    have h3 : (1 - (ENNReal.ofReal a * V).toReal) ^ n
        ≤ (Real.exp (-(ENNReal.ofReal a * V).toReal)) ^ n :=
      pow_le_pow_left₀ (by linarith) h1w n
    rw [← Real.exp_nat_mul (-(ENNReal.ofReal a * V).toReal) n] at h3
    have h4 : (n : ℝ) * (-(ENNReal.ofReal a * V).toReal)
        = -((n : ℝ) * (ENNReal.ofReal a * V).toReal) := by ring
    rw [h4] at h3
    calc (1 - t) ^ n
        ≤ (1 - ENNReal.ofReal a * V) ^ n := hpm n
    _ = ENNReal.ofReal (1 - (ENNReal.ofReal a * V).toReal) ^ n := by rw [h1W]
    _ = ENNReal.ofReal ((1 - (ENNReal.ofReal a * V).toReal) ^ n) :=
      (ENNReal.ofReal_pow (by linarith) n).symm
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * (ENNReal.ofReal a * V).toReal))) :=
      ENNReal.ofReal_le_ofReal h3
    _ = expBound (n * a) V := by rw [hex, htr]

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f)
    (s : Finset X) (hs : ∀ q ∈ s, c * δ ≤ f q)
    (hcover : superlevel f (c * δ) ⊆ ⋃ q ∈ s, Metric.closedBall q (δ / 8)) :
    sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ≤ ((s.card : ℕ∞) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) := by
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens
  -- the single-sample law is a probability measure (S1 template, verbatim)
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  -- per-ball density lower bound: on B(q, δ/8) the Lipschitz f-step gives f ≥ ¾·c·δ,
  -- hence ν B ≥ ofReal (¾·c·δ) * μ B ≥ ofReal (¾·c·δ) * V (q ∈ F, so `iInf₂_le`)
  have hball : ∀ q ∈ s, ENNReal.ofReal (3 / 4 * c * δ) *
      minBallMeasure μ (δ / 8) (superlevel f (c * δ))
      ≤ sampleLaw μ f (Metric.closedBall q (δ / 8)) := by
    intro q hq
    have hqF : q ∈ superlevel f (c * δ) := hs q hq
    have hfq : ∀ p ∈ Metric.closedBall q (δ / 8), 3 / 4 * c * δ ≤ f p := by
      intro p hp
      have h1 : c * δ ≤ f q := hqF
      have h2 : dist p q ≤ δ / 8 := hp
      have h3 : |f p - f q| ≤ c * dist p q := hLip p q
      have hcd : 0 ≤ c * δ := mul_nonneg hc.le hδ.le
      have h4 : c * dist p q ≤ c * (δ / 8) := mul_le_mul_of_nonneg_left h2 hc.le
      have h5 := (abs_le.mp h3).1
      nlinarith
    have hBm : MeasurableSet (Metric.closedBall q (δ / 8)) := measurableSet_closedBall
    calc ENNReal.ofReal (3 / 4 * c * δ) * minBallMeasure μ (δ / 8) (superlevel f (c * δ))
        ≤ ENNReal.ofReal (3 / 4 * c * δ) * μ (Metric.closedBall q (δ / 8)) :=
      mul_le_mul' le_rfl (iInf₂_le q hqF)
    _ = ∫⁻ p in Metric.closedBall q (δ / 8), ENNReal.ofReal (3 / 4 * c * δ) ∂μ :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ p in Metric.closedBall q (δ / 8), ENNReal.ofReal (f p) ∂μ :=
      setLIntegral_mono' hBm (fun p hp => ENNReal.ofReal_le_ofReal (hfq p hp))
    _ = sampleLaw μ f (Metric.closedBall q (δ / 8)) := (withDensity_apply _ hBm).symm
  -- per-ball event measure: E_q := the pi-box over B_qᶜ, of measure (1 − ν B_q) ^ n
  have hper : ∀ q ∈ s, sampleMeasure μ n f
      {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)}
      ≤ expBound (n * (3 / 4 * c * δ)) (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) := by
    intro q hq
    have hE : {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)}
        = Set.pi ((Finset.univ : Finset (Fin n)) : Set (Fin n))
            (fun _ => (Metric.closedBall q (δ / 8))ᶜ) := by
      ext pts
      simp
    have hBm : MeasurableSet (Metric.closedBall q (δ / 8)) := measurableSet_closedBall
    have hfin : sampleLaw μ f (Metric.closedBall q (δ / 8)) ≠ ⊤ := by
      have h1 : sampleLaw μ f (Metric.closedBall q (δ / 8)) ≤ 1 :=
        (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
      simpa using h1
    have hcomp : sampleLaw μ f (Metric.closedBall q (δ / 8))ᶜ
        = 1 - sampleLaw μ f (Metric.closedBall q (δ / 8)) := by
      rw [measure_compl hBm hfin, measure_univ]
    have hbox : sampleMeasure μ n f
        (Set.pi ((Finset.univ : Finset (Fin n)) : Set (Fin n))
          (fun _ => (Metric.closedBall q (δ / 8))ᶜ))
        = ∏ i ∈ (Finset.univ : Finset (Fin n)),
            sampleLaw μ f (Metric.closedBall q (δ / 8))ᶜ := by
      show Measure.pi (fun _ : Fin n => sampleLaw μ f) (Set.pi ((Finset.univ : Finset (Fin n)) : Set (Fin n))
          (fun _ => (Metric.closedBall q (δ / 8))ᶜ)) = _
      exact Measure.pi_pi_finset _ _ _
    have hprod : ∏ i ∈ (Finset.univ : Finset (Fin n)),
        sampleLaw μ f (Metric.closedBall q (δ / 8))ᶜ
        = (sampleLaw μ f (Metric.closedBall q (δ / 8))ᶜ) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hEeq : sampleMeasure μ n f
        {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)}
        = (1 - sampleLaw μ f (Metric.closedBall q (δ / 8))) ^ n := by
      rw [hE, hbox, hprod, hcomp]
    have ht1 : sampleLaw μ f (Metric.closedBall q (δ / 8)) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
    have hkpos : 0 ≤ 3 / 4 * c * δ :=
      mul_nonneg (mul_nonneg (by norm_num) hc.le) hδ.le
    rw [hEeq]
    exact miss_le_expBound n (3 / 4 * c * δ)
      (minBallMeasure μ (δ / 8) (superlevel f (c * δ)))
      (sampleLaw μ f (Metric.closedBall q (δ / 8))) hkpos (hball q hq) ht1
  -- netting-from-hits: ¬netting ⊆ ⋃ q ∈ s, E_q
  have hsub : {pts : Fin n → X |
      ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ⊆ ⋃ q ∈ s, {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)} := by
    intro pts hpts
    obtain ⟨y, hyF, hyfar⟩ :
        ∃ y ∈ superlevel f (c * δ), ∀ v ∈ Set.range pts, δ / 4 < dist y v := by
      by_contra hcon
      push_neg at hcon
      exact hpts hcon
    obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp (hcover hyF)
    simp only [Set.mem_iUnion₂]
    refine ⟨q, hq, fun i hi => ?_⟩
    have h1 : dist y q ≤ δ / 8 := hqy
    have h2 : dist q (pts i) ≤ δ / 8 := Metric.mem_closedBall'.mp hi
    have hd : dist y (pts i) ≤ δ / 4 := by
      have h3 : dist y (pts i) ≤ dist y q + dist q (pts i) := dist_triangle _ _ _
      have h4 : dist y q + dist q (pts i) ≤ δ / 8 + δ / 8 := add_le_add h1 h2
      linarith
    exact absurd hd (not_le.mpr (hyfar (pts i) ⟨i, rfl⟩))
  -- union bound over the cover Finset + counting step
  calc sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ≤ sampleMeasure μ n f
          (⋃ q ∈ s, {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)}) :=
        measure_mono hsub
  _ ≤ ∑ q ∈ s, sampleMeasure μ n f
        {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)} :=
        measure_biUnion_finset_le s _
  _ ≤ ∑ q ∈ s, expBound (n * (3 / 4 * c * δ))
        (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) :=
        Finset.sum_le_sum (fun q hq => hper q hq)
  _ = ((s.card : ℕ∞) : ENNReal) * expBound (n * (3 / 4 * c * δ))
        (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENat.toENNReal_coe s.card]
