-- Prove2me | solution 1 for WassersteinLinOpt.Ball.ball_uniformly_bounded_moment
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T02:23:33.356994+00:00
-- url     : https://prove2.me/submissions/41df0545-36dd-4037-a1ad-ae66eb396df8

/-
Uniform moment bound on Wasserstein balls, 23 October 2026.
Original mathematics: Man-Chung Yue, Daniel Kuhn and Wolfram Wiesemann,
On linear optimization over Wasserstein balls, Lemma 1, author PDF 7 June 2021,
pp.2–3; published Math. Program. 195 (2022), pp.1107–1122.
mikedeng1 supplied the platform definitions and formal target. Shuze Chen's
statement approval is not review of this proof. No prior platform proof is used.
Alexander Richard Towell directed the campaign and verification standards;
OpenAI Codex constructed this proof and performed the formal checks.
The argument uses the coarse power triangle estimate and an approximately
minimizing coupling, without existence of an optimal coupling or a separate
Wasserstein triangle theorem. Lean/Mathlib supply measure and extended-real
foundations. No mathematical novelty or independent human review is claimed.
-/
import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinMomentProof

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def cost (p : ℝ) (x y : X) : ℝ≥0∞ := ENNReal.ofReal (dist x y) ^ p
noncomputable def moment (p : ℝ) (μ : Measure X) (y : X) : ℝ≥0∞ :=
  ∫⁻ x, cost p x y ∂μ

lemma cost_measurable (p : ℝ) (y : X) : Measurable (fun x : X => cost p x y) := by
  unfold cost
  fun_prop

omit [MeasurableSpace X] [BorelSpace X] in
lemma cost_triangle (p : ℝ) (hp : 0 ≤ p) (x y z : X) :
    cost p x z ≤ (2 : ℝ≥0∞)^p * (cost p x y + cost p y z) := by
  unfold cost
  calc
    ENNReal.ofReal (dist x z) ^ p ≤
        (ENNReal.ofReal (dist x y) + ENNReal.ofReal (dist y z)) ^ p := by
      apply ENNReal.rpow_le_rpow _ hp
      rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg]
      exact ENNReal.ofReal_le_ofReal (dist_triangle x y z)
    _ ≤ _ := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp

lemma moment_change (p : ℝ) (hp : 0 ≤ p) (μ : ProbabilityMeasure X) (y z : X) :
    moment p (μ : Measure X) z ≤ (2 : ℝ≥0∞)^p *
      (moment p (μ : Measure X) y + cost p y z) := by
  calc
    moment p (μ : Measure X) z ≤ ∫⁻ x, (2 : ℝ≥0∞)^p *
        (cost p x y + cost p y z) ∂(μ : Measure X) :=
      lintegral_mono fun x => cost_triangle p hp x y z
    _ = _ := by
      rw [lintegral_const_mul _ (show Measurable (fun x : X => cost p x y + cost p y z) from (cost_measurable p y).add measurable_const),
        lintegral_add_left (cost_measurable p y)]
      simp [moment]

lemma coupling_bound [SecondCountableTopology X] (p : ℝ) (hp : 0 ≤ p)
    (μ ν : ProbabilityMeasure X) (γ : Measure (X × X))
    (hγ : γ ∈ WassersteinLinOpt.Ball.couplings (μ : Measure X) (ν : Measure X))
    (z : X) :
    moment p (μ : Measure X) z ≤ (2 : ℝ≥0∞)^p *
      ((∫⁻ q : X × X, cost p q.1 q.2 ∂γ) + moment p (ν : Measure X) z) := by
  have hc : Measurable (fun q : X × X => cost p q.1 q.2) := by
    unfold cost
    fun_prop
  have hfst : moment p (μ : Measure X) z = ∫⁻ q : X × X, cost p q.1 z ∂γ := by
    rw [moment, ← hγ.1, lintegral_map (cost_measurable p z) measurable_fst]
  have hsnd : moment p (ν : Measure X) z = ∫⁻ q : X × X, cost p q.2 z ∂γ := by
    rw [moment, ← hγ.2, lintegral_map (cost_measurable p z) measurable_snd]
  rw [hfst, hsnd]
  calc
    (∫⁻ q : X × X, cost p q.1 z ∂γ) ≤
        ∫⁻ q : X × X, (2 : ℝ≥0∞)^p * (cost p q.1 q.2 + cost p q.2 z) ∂γ :=
      lintegral_mono fun q => cost_triangle p hp q.1 q.2 z
    _ = _ := by
      rw [lintegral_const_mul _ (show Measurable (fun q : X × X => cost p q.1 q.2 + cost p q.2 z) from hc.add ((cost_measurable p z).comp measurable_snd)),
        lintegral_add_left hc]

end WassersteinMomentProof

open WassersteinMomentProof WassersteinLinOpt.Ball

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) (x₀ : X) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X) ≤ ENNReal.ofReal C := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hK : (2 : ℝ≥0∞)^p ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 (by norm_num)).ne
  obtain ⟨y, hy⟩ := hν
  have hy' : moment p (ν : Measure X) y < ⊤ := by
    simpa only [moment, cost, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0] using hy
  have hcost : cost p y x₀ ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 ENNReal.ofReal_ne_top).ne
  have hN : moment p (ν : Measure X) x₀ ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (moment_change p hp0 ν y x₀)
    exact ENNReal.mul_ne_top hK (ENNReal.add_ne_top.mpr ⟨hy'.ne, hcost⟩)
  let R : ℝ≥0∞ := (ENNReal.ofReal r)^p + 1
  have hrpow : (ENNReal.ofReal r)^p ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hp0 ENNReal.ofReal_ne_top).ne
  have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hrpow, by norm_num⟩
  let B : ℝ≥0∞ := (2 : ℝ≥0∞)^p * (R + moment p (ν : Measure X) x₀)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hK (ENNReal.add_ne_top.mpr ⟨hR, hN⟩)
  refine ⟨B.toReal + 1, by positivity, ?_⟩
  intro μ hμ
  have hw : (⨅ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ q : X × X, cost p q.1 q.2 ∂γ) ^ (1 / p) ≤ ENNReal.ofReal r := by
    simpa only [wassersteinBall, Set.mem_ofPred_eq, wassersteinDist, cost,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0] using hμ
  have hinf : (⨅ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ q : X × X, cost p q.1 q.2 ∂γ) ≤ (ENNReal.ofReal r)^p := by
    exact (ENNReal.rpow_inv_le_iff hp_pos).mp (by simpa only [one_div] using hw)
  have hlt : (⨅ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ q : X × X, cost p q.1 q.2 ∂γ) < R :=
    lt_of_le_of_lt hinf (ENNReal.lt_add_right hrpow (by norm_num))
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hγmem, hγcost⟩ := iInf_lt_iff.mp hγ
  have hmoment : moment p (μ : Measure X) x₀ ≤ B := by
    apply (coupling_bound p hp0 μ ν γ hγmem x₀).trans
    dsimp [B]
    gcongr
  have hBreal : B ≤ ENNReal.ofReal (B.toReal + 1) := by
    calc
      B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hB).symm
      _ ≤ ENNReal.ofReal (B.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  simpa only [moment, cost, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0]
    using hmoment.trans hBreal

#print axioms solution
