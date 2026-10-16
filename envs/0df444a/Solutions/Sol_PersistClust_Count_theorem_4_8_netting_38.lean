-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_netting_38
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-16T05:29:48.142193+00:00
-- url     : https://prove2.me/submissions/c33e5c83-bf8a-4370-9a4f-767b4aa8b10f

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

namespace PersistClust.Count

/-- The `(1 − t)^n ≤ expBound (n * a) V` step, abstractly: if `t ≥ ofReal a * V` and `t ≤ 1`
then the probability of missing a fixed ball with all `n` samples is at most `expBound (n * a) V`.
(The analytic content: `(1 − w) ^ n ≤ e ^ (-(n * w))` via `1 − w ≤ e ^ (−w)`, `pow_le_pow_left₀`
and `Real.exp_nat_mul`; the `ofReal a * V = ∞` case is void since it forces `t = ∞ > 1`.) -/
private theorem miss_le_expBound (n : ℕ) (a : ℝ) (V t : ℝ≥0∞) (ha : 0 ≤ a)
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

/-- S3 (3δ/8 netting), internal δ/4-cover form: the root's `V` token VERBATIM, count = size of a given
internal cover (an infimum version over internal covers follows since ℕ-valued infima
are attained). -/
theorem s3n_int38 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f)
    (s : Finset X) (hs : ∀ q ∈ s, c * δ ≤ f q)
    (hcover : superlevel f (c * δ) ⊆ ⋃ q ∈ s, Metric.closedBall q (δ / 4)) :
    sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
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
      ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
      ⊆ ⋃ q ∈ s, {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)} := by
    intro pts hpts
    obtain ⟨y, hyF, hyfar⟩ :
        ∃ y ∈ superlevel f (c * δ), ∀ v ∈ Set.range pts, 3 * δ / 8 < dist y v := by
      by_contra hcon
      push_neg at hcon
      exact hpts hcon
    obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp (hcover hyF)
    simp only [Set.mem_iUnion₂]
    refine ⟨q, hq, fun i hi => ?_⟩
    have h1 : dist y q ≤ δ / 4 := hqy
    have h2 : dist q (pts i) ≤ δ / 8 := Metric.mem_closedBall'.mp hi
    have hd : dist y (pts i) ≤ 3 * δ / 8 := by
      have h3 : dist y (pts i) ≤ dist y q + dist q (pts i) := dist_triangle _ _ _
      have h4 : dist y q + dist q (pts i) ≤ δ / 4 + δ / 8 := add_le_add h1 h2
      linarith
    exact absurd hd (not_le.mpr (hyfar (pts i) ⟨i, rfl⟩))
  -- union bound over the cover Finset + counting step
  calc sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
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

/-- **The netting bound with the original 4.8 pairing.** The probability that the sample fails
to be a geodesic `3δ/8`-sample of `𝔽^{cδ}` is at most the EXTERNAL covering number
`𝒩_{δ/8}(𝔽^{cδ})` times `e^{−n·(3/4)cδ·𝒱_{δ/8}(𝔽^{cδ})}` with the `𝔽^{cδ}`-CENTRED ball
measure. The unjustified comparison of the paper (external ball volume ≥ `𝒱`) is avoided:
each ball of a minimal external cover that meets `𝔽^{cδ}` is replaced by the ball of the same
radius centred at a point of `𝔽^{cδ}` inside it; these points cover `𝔽^{cδ}` at radius `δ/4`
(two hops of `δ/8`), and a hit in each of their `δ/8`-balls nets `𝔽^{cδ}` at `δ/4 + δ/8`. -/
theorem s3n_ext38 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f) :
    sampleMeasure μ n f
        {pts : Fin n → X |
          ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) := by
  classical
  have hdens' := hdens
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens'
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  have hk : 0 < 3 / 4 * c * δ := mul_pos (mul_pos (by norm_num) hc) hδ
  have hkpos : 0 ≤ 3 / 4 * c * δ := hk.le
  by_cases hcn : coveringNumber (δ / 8) (superlevel f (c * δ)) = ⊤
  · -- coveringNumber = ⊤: the F-centred V is finite (an F-centred ball has ν-mass
    -- ≥ k · μ-ball and ν ≤ 1), hence expBound ≠ 0 and the RHS is ⊤
    have hFne : (superlevel f (c * δ)).Nonempty := by
      by_contra hFemp
      have hF : superlevel f (c * δ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hFemp
      have h0 : coveringNumber (δ / 8) (superlevel f (c * δ))
          ≤ ((∅ : Finset X).card : ℕ∞) :=
        iInf₂_le ∅ (by rw [hF]; exact Set.empty_subset _)
      rw [hcn] at h0
      exact absurd h0 (by simp)
    obtain ⟨q₀, hq₀⟩ := hFne
    have hfq₀ : ∀ p ∈ Metric.closedBall q₀ (δ / 8), 3 / 4 * c * δ ≤ f p := by
      intro p hp
      have h1 : c * δ ≤ f q₀ := hq₀
      have h2 : dist p q₀ ≤ δ / 8 := hp
      have h3 : |f p - f q₀| ≤ c * dist p q₀ := hLip p q₀
      have hcd : 0 ≤ c * δ := mul_nonneg hc.le hδ.le
      have h4 : c * dist p q₀ ≤ c * (δ / 8) := mul_le_mul_of_nonneg_left h2 hc.le
      have h5 := (abs_le.mp h3).1
      nlinarith
    have hBm₀ : MeasurableSet (Metric.closedBall q₀ (δ / 8)) := measurableSet_closedBall
    have hball₀ : ENNReal.ofReal (3 / 4 * c * δ) *
        minBallMeasure μ (δ / 8) (superlevel f (c * δ))
        ≤ sampleLaw μ f (Metric.closedBall q₀ (δ / 8)) := by
      calc ENNReal.ofReal (3 / 4 * c * δ) * minBallMeasure μ (δ / 8) (superlevel f (c * δ))
          ≤ ENNReal.ofReal (3 / 4 * c * δ) * μ (Metric.closedBall q₀ (δ / 8)) :=
        mul_le_mul' le_rfl (iInf₂_le q₀ hq₀)
      _ = ∫⁻ p in Metric.closedBall q₀ (δ / 8), ENNReal.ofReal (3 / 4 * c * δ) ∂μ :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ p in Metric.closedBall q₀ (δ / 8), ENNReal.ofReal (f p) ∂μ :=
        setLIntegral_mono' hBm₀ (fun p hp => ENNReal.ofReal_le_ofReal (hfq₀ p hp))
      _ = sampleLaw μ f (Metric.closedBall q₀ (δ / 8)) := (withDensity_apply _ hBm₀).symm
    have ht1₀ : sampleLaw μ f (Metric.closedBall q₀ (δ / 8)) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
    have hVne : minBallMeasure μ (δ / 8) (superlevel f (c * δ)) ≠ ⊤ := by
      by_contra hVtop
      rw [hVtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hk)] at hball₀
      exact absurd (le_trans hball₀ ht1₀) (by simp)
    have hne : ENNReal.ofReal (n * (3 / 4 * c * δ))
        * minBallMeasure μ (δ / 8) (superlevel f (c * δ)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_toReal hVne,
        ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg n) hkpos)]
      exact ENNReal.ofReal_ne_top
    have hEne : expBound (n * (3 / 4 * c * δ))
        (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) ≠ 0 := by
      have hex' : expBound (n * (3 / 4 * c * δ))
          (minBallMeasure μ (δ / 8) (superlevel f (c * δ)))
          = ENNReal.ofReal (Real.exp (-(ENNReal.ofReal (n * (3 / 4 * c * δ))
            * minBallMeasure μ (δ / 8) (superlevel f (c * δ))).toReal)) := by
        simp only [expBound]
        rw [if_neg hne]
      rw [hex']
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    rw [hcn, ENat.toENNReal_top, ENNReal.top_mul hEne]
    exact le_top
  · -- coveringNumber ≠ ⊤: extract an external cover with card ≤ coveringNumber
    have hkey : coveringNumber (δ / 8) (superlevel f (c * δ))
        < coveringNumber (δ / 8) (superlevel f (c * δ)) + 1 :=
      (ENat.lt_add_one_iff hcn).mpr le_rfl
    obtain ⟨s, hinner⟩ := (iInf_lt_iff (f := fun (s : Finset X) =>
        ⨅ (_ : superlevel f (c * δ) ⊆ ⋃ x ∈ s, Metric.closedBall x (δ / 8)), (s.card : ℕ∞))
        (a := coveringNumber (δ / 8) (superlevel f (c * δ)) + 1)).mp hkey
    obtain ⟨hcover, hcard'⟩ := (iInf_lt_iff (f := fun
        (_ : superlevel f (c * δ) ⊆ ⋃ x ∈ s, Metric.closedBall x (δ / 8)) => (s.card : ℕ∞))
        (a := coveringNumber (δ / 8) (superlevel f (c * δ)) + 1)).mp hinner
    have hcardle : (s.card : ℕ∞) ≤ coveringNumber (δ / 8) (superlevel f (c * δ)) :=
      (ENat.lt_add_one_iff hcn).mp hcard'
    -- move every centre whose ball meets F to a point of F inside that ball
    let pick : X → X := fun q =>
      if h : (superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8)).Nonempty then h.some else q
    let s' : Finset X :=
      s.filter (fun q => (superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8)).Nonempty)
    let t : Finset X := s'.image pick
    have hpick : ∀ q ∈ s', pick q ∈ superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8) := by
      intro q hq
      have hmeet := (Finset.mem_filter.mp hq).2
      show (if h : (superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8)).Nonempty
          then h.some else q) ∈ _
      rw [dif_pos hmeet]
      exact hmeet.some_mem
    have ht_in : ∀ p ∈ t, c * δ ≤ f p := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (hpick q hq).1
    have ht_cover : superlevel f (c * δ) ⊆ ⋃ p ∈ t, Metric.closedBall p (δ / 4) := by
      intro y hyF
      obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp (hcover hyF)
      have hqs' : q ∈ s' := Finset.mem_filter.mpr ⟨hq, ⟨y, Set.mem_inter hyF hqy⟩⟩
      refine Set.mem_iUnion₂.mpr ⟨pick q, Finset.mem_image_of_mem pick hqs', ?_⟩
      have h1 : dist y q ≤ δ / 8 := hqy
      have h2 : dist (pick q) q ≤ δ / 8 := (hpick q hqs').2
      have h3 : dist y (pick q) ≤ dist y q + dist q (pick q) := dist_triangle _ _ _
      rw [dist_comm q (pick q)] at h3
      show dist y (pick q) ≤ δ / 4
      linarith
    have htcard : (t.card : ℕ∞) ≤ coveringNumber (δ / 8) (superlevel f (c * δ)) := by
      have h1 : t.card ≤ s'.card := Finset.card_image_le
      have h2 : s'.card ≤ s.card := Finset.card_filter_le _ _
      exact le_trans (Nat.cast_le.mpr (le_trans h1 h2)) hcardle
    calc sampleMeasure μ n f
          {pts : Fin n → X |
            ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
        ≤ ((t.card : ℕ∞) : ENNReal) * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) :=
          s3n_int38 μ f c δ hc hδ n hLip hdens t ht_in ht_cover
      _ ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
          * expBound (n * (3 / 4 * c * δ))
              (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) :=
          mul_le_mul' (ENat.toENNReal_mono htcard) (le_refl _)

end PersistClust.Count

open PersistClust.Count

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f) :
    sampleMeasure μ n f
        {pts : Fin n → X |
          ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (superlevel f (c * δ))) := by
  exact s3n_ext38 μ f c δ hc hδ n hLip hdens
