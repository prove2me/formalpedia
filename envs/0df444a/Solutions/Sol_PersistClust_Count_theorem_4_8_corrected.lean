-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-16T01:01:08.730397+00:00
-- url     : https://prove2.me/submissions/f653122d-426e-45f5-9183-a74434247908

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm
import Theorems.Thm_PersistClust_Count_theorem_4_5
import Theorems.Thm_PersistClust_Count_theorem_4_8_core

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

namespace PersistClust.Count

/-! ## S1 — the sample-positivity null set of the 4.8 probabilistic shell

The accepted core (`PersistClust.Count.theorem_4_8_core`, id 027bdb99) takes the
deterministic positivity hypothesis `hpos : ∀ i : Fin n, 0 < f (pts i)`.  The shell
must show that its failure set `{pts | ∃ i, f (pts i) ≤ 0}` (note: `¬(0 < f (pts i))`
unfolds to `f (pts i) ≤ 0`) is `sampleMeasure`-null.

Only three facts are used: the density normalization `IsDensity μ f` (non-negativity AND
`∫ f dμ = 1` — the latter only to make `sampleLaw μ f` a probability measure, hence
sigma-finite, which `Measure.pi_eval_preimage_null` needs) and measurability of `f`
(in the root it follows from `hLip` via Lipschitz → continuous → measurable, using
`[BorelSpace X]`).  On the level set `{x | f x ≤ 0}` non-negativity forces `f = 0`, so
the density integrand `ENNReal.ofReal ∘ f` vanishes there and each one-coordinate slice
has `sampleLaw μ f {x | f x ≤ 0} = 0`.
`Measure.pi_eval_preimage_null` transports the null slice to the product, and
`measure_iUnion_null_iff` finishes the finite union. -/

theorem s1_pos_null {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (n : ℕ)
    (hdens : IsDensity μ f) (hf : Measurable f) :
    sampleMeasure μ n f {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} = 0 := by
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens
  have hA : MeasurableSet {x : X | f x ≤ 0} := measurableSet_Iic.preimage hf
  -- each one-coordinate slice is null for the single-sample law
  have h0 : sampleLaw μ f {x : X | f x ≤ 0} = 0 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x ≤ 0} = 0
    have h1 : μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x ≤ 0}
        = ∫⁻ a in {x : X | f x ≤ 0}, ENNReal.ofReal (f a) ∂μ :=
      withDensity_apply _ hA
    have h2 : ∫⁻ a in {x : X | f x ≤ 0}, ENNReal.ofReal (f a) ∂μ = 0 := by
      rw [← lintegral_indicator hA]
      have hpt : ∀ a : X,
          {x : X | f x ≤ 0}.indicator (fun x => ENNReal.ofReal (f x)) a = 0 := by
        intro a
        by_cases ha : a ∈ {x : X | f x ≤ 0}
        · have hfa : f a = 0 := le_antisymm ha (hnonneg a)
          rw [Set.indicator_of_mem ha, hfa, ENNReal.ofReal_zero]
        · exact Set.indicator_of_notMem ha (fun x => ENNReal.ofReal (f x))
      rw [lintegral_congr hpt]
      exact lintegral_zero
    rw [h1, h2]
  -- the single-sample law is a probability measure (density normalization), hence
  -- sigma-finite — this is what `Measure.pi_eval_preimage_null` synthesizes
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  have key : ∀ i : Fin n,
      sampleMeasure μ n f {pts : Fin n → X | f (pts i) ≤ 0} = 0 := fun i =>
    Measure.pi_eval_preimage_null (μ := fun _ : Fin n => sampleLaw μ f) h0
  have hU : {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0}
      = ⋃ i : Fin n, {pts : Fin n → X | f (pts i) ≤ 0} := by
    ext pts
    simp
  rw [hU]
  exact measure_iUnion_null_iff (μ := sampleMeasure μ n f) |>.2 key

/-! ## S2 — the τ-genericity null set, CONDITIONAL (the unconditional claim is false)

The core's `hτexc` says: no bar of the sample's Rips diagram is born exactly at `τ` with
death ≤ 0.  Bars of the (superlevel-indexed) Rips filtration are born at vertex values,
so the failure set is contained in `{pts | ∃ i, f (pts i) = τ}`.  That set is null iff
`sampleLaw μ f {x | f x = τ} = 0`, and on `{f = τ}` the integrand is the constant
`ofReal τ` (NOT 0 — the S1 vanishing trick does not apply), so nullity needs
`μ {x | f x = τ} = 0`, which is NOT derivable from the root's hypotheses: a c-Lipschitz
density may be constant (= τ) on a positive-measure set, and with n = 1 a sample point
there makes the sample's essential bar `(τ, ⊥)` — hτexc fails with positive probability.
The paper's Theorem 4.8 proof contains no τ-null-set argument at all (p. 22–24).

PROOF (GREEN, as built): mirror S1, replacing the vanishing-integral step by
  sampleLaw μ f {x | f x = τ}
    = ∫⁻ x in {f = τ}, ofReal (f x) ∂μ
    = ∫⁻ x, ({f = τ}).indicator (fun _ => ENNReal.ofReal τ) x ∂μ   (lintegral_indicator,
      lintegral_congr: on {f = τ} use `f x = τ`; off it both indicators are 0)
    = ∫⁻ x in {f = τ}, ENNReal.ofReal τ ∂μ = ofReal τ * μ {f = τ} = 0   (hτnull).
Then `pi_eval_preimage_null` + `measure_iUnion_null_iff` verbatim as in S1.
-/
theorem s2_tau_null {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (n : ℕ)
    (τ : ℝ) (hdens : IsDensity μ f) (hf : Measurable f) (hτnull : μ {x : X | f x = τ} = 0) :
    sampleMeasure μ n f {pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} = 0 := by
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens
  have hA : MeasurableSet {x : X | f x = τ} := (MeasurableSet.singleton τ).preimage hf
  -- each one-coordinate slice is null for the single-sample law: the S1 machinery with the
  -- vanishing-integral step replaced by the restricted-const step `ofReal τ * μ A = 0`
  have h0 : sampleLaw μ f {x : X | f x = τ} = 0 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x = τ} = 0
    have h1 : μ.withDensity (fun x => ENNReal.ofReal (f x)) {x : X | f x = τ}
        = ∫⁻ a in {x : X | f x = τ}, ENNReal.ofReal (f a) ∂μ :=
      withDensity_apply _ hA
    have h2 : ∫⁻ a in {x : X | f x = τ}, ENNReal.ofReal (f a) ∂μ = 0 := by
      rw [← lintegral_indicator hA]
      -- on the level set the integrand is the constant `ofReal τ`
      have hpt : ∀ a : X, {x : X | f x = τ}.indicator (fun x => ENNReal.ofReal (f x)) a
          = {x : X | f x = τ}.indicator (fun _ => ENNReal.ofReal τ) a := by
        intro a
        by_cases ha : a ∈ {x : X | f x = τ}
        · have hfa : f a = τ := ha
          rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hfa]
        · rw [Set.indicator_of_notMem ha (fun x => ENNReal.ofReal (f x)),
            Set.indicator_of_notMem ha (fun _ => ENNReal.ofReal τ)]
      rw [lintegral_congr hpt, lintegral_indicator hA, setLIntegral_const, hτnull, mul_zero]
    rw [h1, h2]
  -- steps 2–5 of the S1 template, verbatim
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  have key : ∀ i : Fin n,
      sampleMeasure μ n f {pts : Fin n → X | f (pts i) = τ} = 0 := fun i =>
    Measure.pi_eval_preimage_null (μ := fun _ : Fin n => sampleLaw μ f) h0
  have hU : {pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ}
      = ⋃ i : Fin n, {pts : Fin n → X | f (pts i) = τ} := by
    ext pts
    simp
  rw [hU]
  exact measure_iUnion_null_iff (μ := sampleMeasure μ n f) |>.2 key

/-! ## S3 — the netting bound: two PROVABLE forms

The root's RHS pairs the EXTERNAL covering number (`coveringNumber`, balls centered
anywhere in X — see the Setting's definition, `⨅ (s : Finset X) …`) with the
F^{cδ}-CENTERED ball-volume infimum `minBallMeasure μ (δ/8) (superlevel f (c*δ))`.
That pairing is exactly Lemma 4.3's falsified one (5 machine-verified disproofs): the
paper's proof (p. 17) needs `μ (B(x_i, δ/8)) ≥ V` for EXTERNAL centers `x_i`, which fails
on curved manifolds.  The f-step of the paper IS correct for external centers: a ball
meeting `F := superlevel f (c*δ)` contains a witness `p_i` with `f p_i ≥ cδ`, and for any
`p` in that ball `dist p p_i ≤ δ/4`, so `f p ≥ cδ − c*δ/4 = 3/4*c*δ` — matching the root's
`expBound (n * (3/4 * c * δ))`.  Two provable rearrangements:

* `s3_net_ext` below keeps the root's count token verbatim and replaces `V` by the global
  ball infimum `minBallMeasure μ (δ/8) univ` (the paper's own remedy hint: p. 18 case b,
  Bishop–Gunter uniform lower bound on ball volumes = `V_r(X)`).
* `s3_net_int` below keeps the root's `V` token verbatim and replaces the external count
  by the size of any internal (F-centered) cover — with centers `q ∈ F` BOTH steps are
  valid (`f ≥ 7/8*c*δ ≥ 3/4*c*δ` on the ball by Lipschitz, and `μ (ball q) ≥ V` by
  `iInf_le` since `q ∈ F`).  An infimum form over internal covers follows since
  ℕ-valued infima are attained.

SHARED PROOF SKELETON (verified against the paper p. 17–18):
  ¬netting ⊆ ⋃_j E_j,  E_j := {pts | ∀ i, pts i ∉ closedBall q_j (δ/8)}
    (if every cover ball contains a sample point then every y ∈ F is within
     δ/8 + δ/8 = δ/4 of some sample point — `IsGeodesicSample (range pts) F (δ/4)`);
  μ^n (E_j) = ∏_i (1 − sampleLaw μ f B_j) ≤ (1 − k*V)^n ≤ e^{−n*k*V}
    = expBound (n * (3/4 * c * δ)) V   [k = 3/4*c*δ, via 1 − x ≤ e^{−x}];
  product-measure step: `Set.pi univ (fun _ => Bᶜ)` with `Measure.pi_pi`
    (see `pi_eval_preimage_null`'s proof / `closedBall_pi` in
    Mathlib/MeasureTheory/Constructions/Pi.lean);
  union bound over the cover Finset: `measure_biUnion_le_...` / `measure_iUnion_le`.
  ⊤-cases: F = ∅ ⟹ netting vacuous (LHS = 0); F ≠ ∅ ⟹ pick q₀ ∈ F, then
    sampleLaw μ f (closedBall q₀ (δ/8)) ≥ (3/4*c*δ) * μ (closedBall q₀ (δ/8)) and
    sampleLaw ≤ 1 (IsDensity) force V ≤ 4/(3*c*δ) < ⊤, so `n * (3/4*c*δ) * V ≠ ⊤`
    and expBound sits in its `else` branch; `coveringNumber = ⊤` then multiplies ⊤ by a
    positive number. For the minimal-cover extraction in s3_net_ext: the infimum is over
    ℕ-valued cardinals, so it is attained (`Set.Nonempty.sInf_mem` after transporting to a
    set of naturals); filter the minimal external cover to the balls meeting F (they still
    cover F, the cardinal only shrinks). -/

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

/-- S3, internal-cover form: the root's `V` token VERBATIM, count = size of a given
internal cover (an infimum version over internal covers follows since ℕ-valued infima
are attained). -/
theorem s3_net_int {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
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

/-- S3, external-count form: the root's `coveringNumber` token VERBATIM, global `V`.
(Moved after `s3_net_int` so that its proof may reuse `miss_le_expBound`.) -/
theorem s3_net_ext {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f) :
    sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (Set.univ : Set X)) := by
  classical
  obtain ⟨hnonneg, hintegrable, hint⟩ := hdens
  -- the single-sample law is a probability measure (S1 template, verbatim)
  have hνuniv : sampleLaw μ f Set.univ = 1 := by
    show μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hintegrable (ae_of_all μ hnonneg), hint]
    exact ENNReal.ofReal_one
  haveI : IsProbabilityMeasure (sampleLaw μ f) := ⟨hνuniv⟩
  have hk : 0 < 3 / 4 * c * δ := mul_pos (mul_pos (by norm_num) hc) hδ
  have hkpos : 0 ≤ 3 / 4 * c * δ := hk.le
  by_cases hcn : coveringNumber (δ / 8) (superlevel f (c * δ)) = ⊤
  · -- coveringNumber = ⊤: the global V is finite (the ball at any point of the
    -- superlevel has ν-mass ≥ k · μ-ball ≤ 1), hence expBound ≠ 0 and RHS = ⊤
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
        minBallMeasure μ (δ / 8) (Set.univ : Set X)
        ≤ sampleLaw μ f (Metric.closedBall q₀ (δ / 8)) := by
      calc ENNReal.ofReal (3 / 4 * c * δ) * minBallMeasure μ (δ / 8) (Set.univ : Set X)
          ≤ ENNReal.ofReal (3 / 4 * c * δ) * μ (Metric.closedBall q₀ (δ / 8)) :=
        mul_le_mul' le_rfl (iInf₂_le q₀ (Set.mem_univ q₀))
      _ = ∫⁻ p in Metric.closedBall q₀ (δ / 8), ENNReal.ofReal (3 / 4 * c * δ) ∂μ :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ p in Metric.closedBall q₀ (δ / 8), ENNReal.ofReal (f p) ∂μ :=
        setLIntegral_mono' hBm₀ (fun p hp => ENNReal.ofReal_le_ofReal (hfq₀ p hp))
      _ = sampleLaw μ f (Metric.closedBall q₀ (δ / 8)) := (withDensity_apply _ hBm₀).symm
    have ht1₀ : sampleLaw μ f (Metric.closedBall q₀ (δ / 8)) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
    have hVne : minBallMeasure μ (δ / 8) (Set.univ : Set X) ≠ ⊤ := by
      by_contra hVtop
      rw [hVtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hk)] at hball₀
      exact absurd (le_trans hball₀ ht1₀) (by simp)
    have hne : ENNReal.ofReal (n * (3 / 4 * c * δ))
        * minBallMeasure μ (δ / 8) (Set.univ : Set X) ≠ ⊤ := by
      rw [← ENNReal.ofReal_toReal hVne,
        ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg n) hkpos)]
      exact ENNReal.ofReal_ne_top
    have hEne : expBound (n * (3 / 4 * c * δ))
        (minBallMeasure μ (δ / 8) (Set.univ : Set X)) ≠ 0 := by
      have hex' : expBound (n * (3 / 4 * c * δ))
          (minBallMeasure μ (δ / 8) (Set.univ : Set X))
          = ENNReal.ofReal (Real.exp (-(ENNReal.ofReal (n * (3 / 4 * c * δ))
            * minBallMeasure μ (δ / 8) (Set.univ : Set X)).toReal)) := by
        simp only [expBound]
        rw [if_neg hne]
      rw [hex']
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    rw [hcn, ENat.toENNReal_top, ENNReal.top_mul hEne]
    exact le_top
  · -- coveringNumber ≠ ⊤: extract an external cover with card ≤ coveringNumber
    -- (`iInf_lt_iff` at coveringNumber + 1, twice), then filter to the balls
    -- meeting the superlevel (they still cover; the cardinal only shrinks)
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
    obtain ⟨s', hs's, hcard's, hcover', hmeet⟩ : ∃ s' : Finset X, s' ⊆ s
        ∧ (s'.card : ℕ∞) ≤ (s.card : ℕ∞)
        ∧ superlevel f (c * δ) ⊆ ⋃ q ∈ s', Metric.closedBall q (δ / 8)
        ∧ ∀ q ∈ s', (superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8)).Nonempty :=
      ⟨s.filter (fun q => (superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8)).Nonempty),
        Finset.filter_subset
          (fun q => (superlevel f (c * δ) ∩ Metric.closedBall q (δ / 8)).Nonempty) s,
        Nat.cast_le.mpr (Finset.card_filter_le _ _),
        fun y hyF => by
          obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp (hcover hyF)
          exact Set.mem_iUnion₂.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, ⟨y, Set.mem_inter hyF hqy⟩⟩, hqy⟩,
        fun q hq => (Finset.mem_filter.mp hq).2⟩
    -- per-ball density bound, valid at EXTERNAL centers: each kept ball meets the
    -- superlevel at some p₀, and the two-hop triangle (δ/8 + δ/8 = δ/4) gives f ≥ ¾·c·δ
    have hball : ∀ q ∈ s', ENNReal.ofReal (3 / 4 * c * δ) *
        minBallMeasure μ (δ / 8) (Set.univ : Set X)
        ≤ sampleLaw μ f (Metric.closedBall q (δ / 8)) := by
      intro q hq
      obtain ⟨p₀, hp₀⟩ := hmeet q hq
      obtain ⟨hp₀F, hp₀q⟩ : p₀ ∈ superlevel f (c * δ) ∧ p₀ ∈ Metric.closedBall q (δ / 8) := hp₀
      have hfq : ∀ p ∈ Metric.closedBall q (δ / 8), 3 / 4 * c * δ ≤ f p := by
        intro p hp
        have h1 : c * δ ≤ f p₀ := hp₀F
        have h2 : dist p p₀ ≤ δ / 4 := by
          have h2a : dist p q ≤ δ / 8 := hp
          have h2b : dist q p₀ ≤ δ / 8 := by rw [dist_comm]; exact hp₀q
          have htr : dist p p₀ ≤ dist p q + dist q p₀ := dist_triangle p q p₀
          linarith
        have h3 : |f p - f p₀| ≤ c * dist p p₀ := hLip p p₀
        have hcd : 0 ≤ c * δ := mul_nonneg hc.le hδ.le
        have h4 : c * dist p p₀ ≤ c * (δ / 4) := mul_le_mul_of_nonneg_left h2 hc.le
        have h5 := (abs_le.mp h3).1
        nlinarith
      have hBm : MeasurableSet (Metric.closedBall q (δ / 8)) := measurableSet_closedBall
      calc ENNReal.ofReal (3 / 4 * c * δ) * minBallMeasure μ (δ / 8) (Set.univ : Set X)
          ≤ ENNReal.ofReal (3 / 4 * c * δ) * μ (Metric.closedBall q (δ / 8)) :=
        mul_le_mul' le_rfl (iInf₂_le q (Set.mem_univ q))
      _ = ∫⁻ p in Metric.closedBall q (δ / 8), ENNReal.ofReal (3 / 4 * c * δ) ∂μ :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ p in Metric.closedBall q (δ / 8), ENNReal.ofReal (f p) ∂μ :=
        setLIntegral_mono' hBm (fun p hp => ENNReal.ofReal_le_ofReal (hfq p hp))
      _ = sampleLaw μ f (Metric.closedBall q (δ / 8)) := (withDensity_apply _ hBm).symm
    -- per-ball event measure: E_q is the pi-box over B_qᶜ, of measure (1 − ν B_q) ^ n
    have hper : ∀ q ∈ s', sampleMeasure μ n f
        {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)}
        ≤ expBound (n * (3 / 4 * c * δ)) (minBallMeasure μ (δ / 8) (Set.univ : Set X)) := by
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
        show Measure.pi (fun _ : Fin n => sampleLaw μ f)
            (Set.pi ((Finset.univ : Finset (Fin n)) : Set (Fin n))
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
      rw [hEeq]
      exact miss_le_expBound n (3 / 4 * c * δ)
        (minBallMeasure μ (δ / 8) (Set.univ : Set X))
        (sampleLaw μ f (Metric.closedBall q (δ / 8))) hkpos (hball q hq) ht1
    -- netting-from-hits: ¬netting ⊆ ⋃ q ∈ s', E_q (S3 template, verbatim)
    have hsub : {pts : Fin n → X |
        ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
        ⊆ ⋃ q ∈ s', {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)} := by
      intro pts hpts
      obtain ⟨y, hyF, hyfar⟩ :
          ∃ y ∈ superlevel f (c * δ), ∀ v ∈ Set.range pts, δ / 4 < dist y v := by
        by_contra hcon
        push_neg at hcon
        exact hpts hcon
      obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp (hcover' hyF)
      simp only [Set.mem_iUnion₂]
      refine ⟨q, hq, fun i hi => ?_⟩
      have h1 : dist y q ≤ δ / 8 := hqy
      have h2 : dist q (pts i) ≤ δ / 8 := Metric.mem_closedBall'.mp hi
      have hd : dist y (pts i) ≤ δ / 4 := by
        have h3 : dist y (pts i) ≤ dist y q + dist q (pts i) := dist_triangle _ _ _
        have h4 : dist y q + dist q (pts i) ≤ δ / 8 + δ / 8 := add_le_add h1 h2
        linarith
      exact absurd hd (not_le.mpr (hyfar (pts i) ⟨i, rfl⟩))
    -- union bound over the filtered cover + counting step
    calc sampleMeasure μ n f
            {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ≤ sampleMeasure μ n f
          (⋃ q ∈ s', {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)}) :=
        measure_mono hsub
    _ ≤ ∑ q ∈ s', sampleMeasure μ n f
          {pts : Fin n → X | ∀ i, pts i ∉ Metric.closedBall q (δ / 8)} :=
        measure_biUnion_finset_le s' _
    _ ≤ ∑ q ∈ s', expBound (n * (3 / 4 * c * δ))
          (minBallMeasure μ (δ / 8) (Set.univ : Set X)) :=
        Finset.sum_le_sum (fun q hq => hper q hq)
    _ = ((s'.card : ℕ∞) : ENNReal) * expBound (n * (3 / 4 * c * δ))
          (minBallMeasure μ (δ / 8) (Set.univ : Set X)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENat.toENNReal_coe s'.card]
    _ ≤ ((coveringNumber (δ / 8) (superlevel f (c * δ)) : ℕ∞) : ENNReal)
          * expBound (n * (3 / 4 * c * δ))
          (minBallMeasure μ (δ / 8) (Set.univ : Set X)) :=
        mul_le_mul' (ENat.toENNReal_mono (le_trans hcard's hcardle)) (le_refl _)


/-- **STUB 3 (optional; the two PRIMARY stubs are gamma_hyp and core_hyp).**
The tau-excision bridge: if no sample value equals tau, then the sample's Rips
diagram has NO bar born exactly at tau with death <= 0. Proof sketch
(stage-constancy argument; see the section header):
- the finite value set image (f o pts) univ avoids tau by a positive gap
  (the min of |f (pts i) - tau| over the nonempty Finset-image; any positive
  number if the image is empty),
- so for every 0 < eps < gap the upper-star stages at tau - eps and tau + eps
  COINCIDE (no vertex value lies in [tau - eps, tau + eps)), hence
  ripsRank ... (tau - eps) t = ripsRank ... (tau + eps) t for every t,
- so every rank difference in `mult`'s infimum vanishes at
  eps0 < min(gap, (tau - d)/2): EReal case split on d (rec on EReal:
  bot / coe / top; top is excluded by hd), the outer if-conditions by
  EReal.coe_ne_bot / coe_ne_top, the d-real branch's `p.2 < p.1` by
  coe_lt_coe (d <= 0 < tau), the `.toReal`s by EReal.toReal_coe, the infimum
  upper bound by iInf2_le at eps0 with tsub_self (twice in the 4-term
  branch), the lower bound by zero_le, le_antisymm to conclude. -/
theorem tauexc_hyp {X : Type*} [MetricSpace X] {n : ℕ} (f : X → ℝ) (τ : ℝ) (δ : ℝ)
    (pts : Fin n → X) (hτ : 0 < τ) (hne : ∀ i : Fin n, f (pts i) ≠ τ)
    (d : EReal) (hd : d ≤ ((0 : ℝ) : EReal)) :
    ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ (((τ : ℝ) : EReal), d) = 0 := by
  -- PLAN (tauExc2): ripsDiagram Dm (f o pts) delta (coe tau, d) unfolds to
  -- mult (ripsRank Dm (f o pts) delta) (coe tau, d). Outer ifs: coe tau != bot / != top
  -- (EReal.coe_ne_bot, EReal.coe_ne_top); p.1.toReal = tau (EReal.toReal_coe).
  -- CASES on d : EReal (bot / coe d' / top); top excluded by hd via EReal.coe_lt_top;
  -- coe d': d' <= 0 (coe_le_coe) so p.2 < p.1 by coe_lt_coe (d' <= 0 < htau).
  --   bot d  : M = INF eps 0<eps, INF t (t <= tau-eps), r (tau-eps) t - r (tau+eps) t.
  --   coe d' : 4-term INF over eps in Set.Ioo 0 ((tau - d')/2).
  -- GAP: S := image (fun i => |f (pts i) - tau|) univ. Empty (n = 0): stage sets are all
  -- empty so the two levels agree for any eps. Nonempty: gamma := S.min' > 0 (elements
  -- positive by hne) and gamma <= |f (pts i) - tau| for all i (Finset.min'_le).
  -- STAGE-CONSTANCY: pick eps0 with 0 < eps0 < gamma (also eps0 < (tau-d')/2 in coe case);
  -- no g i in [tau-eps0, tau+eps0), so {i | tau-eps0 <= g i} = {i | tau+eps0 <= g i},
  -- hence ripsRank Dm g delta (tau-eps0) = ripsRank Dm g delta (tau+eps0) (rank depends
  -- only on the stage set / joined relation at the level).
  -- BOUNDS: upper by iInf2_le at eps0, differences collapse via tsub_self (twice in the
  -- 4-term branch); lower by zero_le + le_iInf; conclude le_antisymm.
  -- FILL (tauExc3): three-case mult evaluation via EReal.rec on the death coordinate,
  -- per the banked plan above: gap gamma, stage-constancy window, rank agreement, then
  -- le_antisymm (upper: iInf_le_of_le at eps0 where the bracket collapses by tsub_self;
  -- lower: le_iInf with the canonically-ordered ENat zero_le).
  have hgap : ∃ γ : ℝ, 0 < γ ∧ ∀ i : Fin n, γ ≤ |(f ∘ pts) i - τ| := by
    rcases isEmpty_or_nonempty (Fin n) with hempty | hne'
    · haveI : IsEmpty (Fin n) := hempty
      exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0⟩ := hne'
      have hSne : (Finset.univ.image fun i : Fin n => |(f ∘ pts) i - τ|).Nonempty :=
        ⟨|(f ∘ pts) i0 - τ|, Finset.mem_image_of_mem _ (Finset.mem_univ i0)⟩
      refine ⟨(Finset.univ.image fun i : Fin n => |(f ∘ pts) i - τ|).min' hSne, ?_, fun i => ?_⟩
      · obtain ⟨i1, -, hmem⟩ := Finset.mem_image.mp (Finset.min'_mem _ hSne)
        rw [← hmem]
        exact abs_pos.mpr (sub_ne_zero.mpr (hne i1))
      · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  obtain ⟨γ, hγpos, hγle⟩ := hgap
  have hsets : ∀ ε : ℝ, 0 < ε → ε < γ →
      {i : Fin n | τ - ε ≤ (f ∘ pts) i} = {i : Fin n | τ + ε ≤ (f ∘ pts) i} := by
    intro ε hεpos hεγ
    ext i
    constructor
    · intro h
      have h' : τ - ε ≤ (f ∘ pts) i := h
      rcases le_or_gt (τ + ε) ((f ∘ pts) i) with hge | hlt
      · exact hge
      · have habs : |(f ∘ pts) i - τ| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
        exact absurd (le_trans (hγle i) habs) (by linarith)
    · intro h
      have h' : τ + ε ≤ (f ∘ pts) i := h
      show τ - ε ≤ (f ∘ pts) i
      linarith
  have hstage : ∀ s1 s2 : ℝ, {i : Fin n | s1 ≤ (f ∘ pts) i} = {i : Fin n | s2 ≤ (f ∘ pts) i} →
      ∀ t : ℝ, ripsRank (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ s1 t
          = ripsRank (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ s2 t := by
    intro s1 s2 hs t
    show ((fun x : Fin n => {y : Fin n | ripsJoined (fun i j => dist (pts i) (pts j))
          (f ∘ pts) δ t x y}) '' {i : Fin n | s1 ≤ (f ∘ pts) i}).encard
        = ((fun x : Fin n => {y : Fin n | ripsJoined (fun i j => dist (pts i) (pts j))
          (f ∘ pts) δ t x y}) '' {i : Fin n | s2 ≤ (f ∘ pts) i}).encard
    rw [hs]
  show mult (ripsRank (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ) (((τ : ℝ) : EReal), d) = 0
  induction d using EReal.rec with
  | bot =>
    unfold mult
    rw [if_pos ⟨EReal.coe_ne_bot τ, EReal.coe_ne_top τ⟩, if_pos rfl]
    simp only [EReal.toReal_coe]
    have hεpos : 0 < γ / 2 := half_pos hγpos
    have hset : {i : Fin n | τ - γ / 2 ≤ (f ∘ pts) i}
        = {i : Fin n | τ + γ / 2 ≤ (f ∘ pts) i} := hsets (γ / 2) hεpos (by linarith)
    refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
      (zero_le : (0 : ℕ∞) ≤ _))
    refine iInf_le_of_le (γ / 2) (iInf_le_of_le hεpos (iInf_le_of_le (τ - γ / 2)
      (iInf_le_of_le (le_refl _) ?_)))
    rw [hstage (τ - γ / 2) (τ + γ / 2) hset (τ - γ / 2), tsub_self]
  | coe d' =>
    have hd'le : d' ≤ 0 := EReal.coe_le_coe_iff.mp hd
    unfold mult
    rw [if_pos ⟨EReal.coe_ne_bot τ, EReal.coe_ne_top τ⟩, if_neg (EReal.coe_ne_bot d'),
        if_pos (EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt hd'le hτ))]
    simp only [EReal.toReal_coe]
    have hpos : 0 < min (γ / 2) ((τ - d') / 4) :=
      lt_min (half_pos hγpos) (div_pos (by linarith) (by norm_num))
    have hw : min (γ / 2) ((τ - d') / 4) < (τ - d') / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hγm : min (γ / 2) ((τ - d') / 4) < γ :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hset : {i : Fin n | τ - min (γ / 2) ((τ - d') / 4) ≤ (f ∘ pts) i}
        = {i : Fin n | τ + min (γ / 2) ((τ - d') / 4) ≤ (f ∘ pts) i} :=
      hsets _ hpos hγm
    refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ =>
      (zero_le : (0 : ℕ∞) ≤ _))
    refine iInf_le_of_le (min (γ / 2) ((τ - d') / 4)) (iInf_le_of_le ⟨hpos, hw⟩ ?_)
    rw [hstage _ _ hset (d' + min (γ / 2) ((τ - d') / 4)),
        hstage _ _ hset (d' - min (γ / 2) ((τ - d') / 4)),
        tsub_self, zero_tsub]
  | top =>
    exact absurd hd (not_le.mpr (EReal.coe_lt_top 0))


end PersistClust.Count

open PersistClust.Count

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X] [MeasurableSpace X] [BorelSpace X]
    (hconv : 0 < convexityRadius X)
    (f : X → ℝ) (c : ℝ) (hc : 0 < c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (hdens : IsDensity (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f) (htame : IsTame0 f)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hsep : IsSeparated (diagram0 f) d₁ d₂)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) (hτnull : (μH[(Module.finrank ℝ E : ℝ)] : Measure X) {x : X | f x = τ} = 0) (n : ℕ) :
    sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
        {pts | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (δ / 8)
              (Set.univ : Set X))
  := by
  classical
  have hcδ : (0 : ℝ) < c * δ := mul_pos hc hδ
  have hτ : (0 : ℝ) < τ := by linarith
  have hl : LipschitzWith (⟨c, hc.le⟩ : NNReal) f :=
    lipschitzWith_iff_dist_le_mul.mpr fun x y => hLip x y
  have hf : Measurable f := hl.continuous.measurable
  have hdecomp : {pts | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ⊆ {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} ∪
        ({pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} ∪
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}) := by
    intro pts hfail
    by_cases h1 : ∃ i : Fin n, f (pts i) ≤ 0
    · exact Or.inl h1
    · push_neg at h1
      right
      by_cases h2 : ∃ i : Fin n, f (pts i) = τ
      · exact Or.inl h2
      · push_neg at h2
        right
        by_cases h3 : IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)
        · exfalso
          obtain ⟨L, hLdef⟩ : ∃ L : Finset X, L = Finset.image pts Finset.univ :=
            ⟨_, rfl⟩
          have hmem : ∀ i : Fin n, pts i ∈ L := by
            intro i
            rw [hLdef]
            exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
          have hsurj : ∀ x ∈ L, ∃ i : Fin n, pts i = x := by
            intro x hx
            rw [hLdef] at hx
            obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
            exact ⟨i, hi⟩
          have hnet : IsGeodesicSample (L : Set X) (superlevel f (c * δ)) (δ / 4) := by
            intro y hyY
            obtain ⟨v, hv, hdv⟩ := h3 y hyY
            obtain ⟨i, hi⟩ := Set.mem_range.mp hv
            refine ⟨pts i, ?_, ?_⟩
            · rw [Finset.mem_coe, hLdef]
              exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
            · rw [hi]
              exact hdv
          have hτexc : ∀ d : EReal, d ≤ ((0 : ℝ) : EReal) →
              ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ
                (((τ : ℝ) : EReal), d) = 0 :=
            fun d hd => tauexc_hyp f τ δ pts hτ h2 d hd
          obtain ⟨γ, hγ⟩ := theorem_4_5 (I := I) hconv L f c hc.le hLip htame δ hδ hδρ (c * δ) hnet
          exact hfail (theorem_4_8_core (I := I) hconv f c hc hLip hdens htame d₁ d₂ hd₁ hd hsep δ hδ hδρ
            hδc τ hτ₁ hτ₂ n pts L hmem hsurj hnet h1 hτexc γ hγ)
        · exact h3
  calc sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
        {pts | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ≤ sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          ({pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} ∪
          ({pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} ∪
          {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)})) :=
        measure_mono hdecomp
  _ ≤ sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} +
        sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          ({pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} ∪
          {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}) :=
        measure_union_le _ _
  _ ≤ sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          {pts : Fin n → X | ∃ i : Fin n, f (pts i) ≤ 0} +
        (sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          {pts : Fin n → X | ∃ i : Fin n, f (pts i) = τ} +
        sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}) :=
        add_le_add (le_refl _) (measure_union_le _ _)
  _ = 0 + (0 + sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
          {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}) := by
        rw [s1_pos_null (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f n hdens hf,
            s2_tau_null (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f n τ hdens hf hτnull]
  _ ≤ 0 + (0 + ((coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal) *
        expBound (n * (3 / 4 * c * δ))
          (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (δ / 8)
            (Set.univ : Set X)))) := by
        exact add_le_add (le_refl _) (add_le_add (le_refl _) (s3_net_ext
          (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f c δ hc hδ n hLip hdens))
  _ = (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal) *
        expBound (n * (3 / 4 * c * δ))
          (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (δ / 8)
            (Set.univ : Set X)) := by
        simp
