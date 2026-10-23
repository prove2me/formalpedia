-- Prove2me | solution 1 for WassersteinLinOpt.Ball.ball_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T04:43:48.802271+00:00
-- url     : https://prove2.me/submissions/d0813959-fe0d-4302-8a4e-a745ca8d49d8

/-
Weak compactness of Wasserstein balls, 23 October 2026.
Original result: Man-Chung Yue, Daniel Kuhn and Wolfram Wiesemann,
On linear optimization over Wasserstein balls, Theorem 1 (published p.1109),
author PDF 7 June 2021, https://manchungyue.com/wasserstein.pdf,
SHA256 d18b8b4c5811c379c9d0e20d444e61047dcfdcdb5b64c4f8b633ab974cbac337.
Platform formalization and definitions: mikedeng1.
This proof reuses the complete accepted uniform-moment proof (target
b635b1fe-a523-4227-b1b0-c24822a18ac5, submission
41df0545-36dd-4037-a1ad-ae66eb396df8, source SHA256
a1f41ce698e93f9c8417baca1cefd8db3660ef72064d54bb7afaefa8ba7d884f)
and the locally verified tightness/compact-closure proof from this campaign.
The new argument proves compactness of fixed-marginal couplings, lower
semicontinuity and attainment of transport cost, and represents the ball as the
continuous projection of a compact constrained coupling set. Lean/Mathlib
supply Prokhorov, Portmanteau, probability-measure topology and foundations.
Alexander Richard Towell directed the research and verification standards;
OpenAI Codex constructed and formally checked the proof. No mathematical
novelty or independent human proof review is claimed. Statement approval is
not proof review. The retained uniform-moment attribution follows.
-/
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


namespace ReusedTightness

namespace ReusedUniformMoment

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

end ReusedUniformMoment

/- Uniform moment bounds imply tightness and compact closure. This is a local
support theorem, not a proof that the Wasserstein ball itself is closed.
Reuses the accepted uniform moment proof above with its attribution retained. -/
open MeasureTheory
open scoped ENNReal NNReal
open WassersteinLinOpt.Ball

namespace WassersteinTightness

lemma tight_of_uniform_moment {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (S : Set (ProbabilityMeasure X))
    (x₀ : X) (p C : ℝ) (hp : 1 ≤ p) (hC : 0 < C)
    (hbound : ∀ μ ∈ S,
      ∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X) ≤ ENNReal.ofReal C) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases htop : ε = ⊤
  · subst ε
    exact ⟨∅, isCompact_empty, by simp⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
  let R : ℝ := C / ε.toReal + 1
  have hRone : 1 ≤ R := by
    dsimp [R]
    have := div_nonneg hC.le he.le
    linarith
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  refine ⟨Metric.closedBall x₀ R, isCompact_closedBall x₀ R, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have hsub : (Metric.closedBall x₀ R)ᶜ ⊆
      {x | ENNReal.ofReal R ≤ ENNReal.ofReal (dist x x₀ ^ p)} := by
    intro x hx
    have hxR : R < dist x x₀ := by simpa only [Set.mem_compl_iff,
      Metric.mem_closedBall, not_le] using hx
    have hxone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (dist x x₀) := by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (hRone.trans hxR.le))
    change ENNReal.ofReal R ≤ ENNReal.ofReal (dist x x₀ ^ p)
    rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0]
    exact (ENNReal.ofReal_le_ofReal hxR.le).trans
      (ENNReal.le_rpow_self_of_one_le hxone hp)
  have hmeas : Measurable (fun x : X => ENNReal.ofReal (dist x x₀ ^ p)) := by
    simp_rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp0]
    fun_prop
  have hratio : C / R ≤ ε.toReal := by
    apply (div_le_iff₀ hR).mpr
    dsimp [R]
    field_simp
    nlinarith
  calc
    (μ : Measure X) (Metric.closedBall x₀ R)ᶜ ≤
        (μ : Measure X) {x | ENNReal.ofReal R ≤ ENNReal.ofReal (dist x x₀ ^ p)} :=
      measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (dist x x₀ ^ p) ∂(μ : Measure X)) /
        ENNReal.ofReal R := meas_ge_le_lintegral_div hmeas.aemeasurable
          (by simpa using hR) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal R := by gcongr; exact hbound μ hμ
    _ = ENNReal.ofReal (C / R) := (ENNReal.ofReal_div_of_pos hR).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hratio
    _ = ε := ENNReal.ofReal_toReal htop

end WassersteinTightness

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) |
      μ ∈ wassersteinBall p r ν} ∧ IsCompact (closure (wassersteinBall p r ν)) := by
  obtain ⟨x₀, hx₀⟩ := hν
  have hν' : HasFinitePthMoment p (ν : Measure X) := ⟨x₀, hx₀⟩
  obtain ⟨C, hC, hbound⟩ := ReusedUniformMoment.solution p r hp hr ν hν' x₀
  have ht := WassersteinTightness.tight_of_uniform_moment
    (wassersteinBall p r ν) x₀ p C hp hC hbound
  exact ⟨ht, isCompact_closure_of_isTightMeasureSet ht⟩

#print axioms solution

end ReusedTightness

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology
open WassersteinLinOpt.Ball
set_option autoImplicit false

namespace CouplingResearch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

noncomputable def first (γ : ProbabilityMeasure (X × X)) : ProbabilityMeasure X :=
  γ.map measurable_fst.aemeasurable

noncomputable def second (γ : ProbabilityMeasure (X × X)) : ProbabilityMeasure X :=
  γ.map measurable_snd.aemeasurable

lemma first_continuous : Continuous (first (X := X)) :=
  ProbabilityMeasure.continuous_map continuous_fst

lemma second_continuous : Continuous (second (X := X)) :=
  ProbabilityMeasure.continuous_map continuous_snd

lemma coupling_iff (γ : ProbabilityMeasure (X × X)) (μ ν : ProbabilityMeasure X) :
    (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X) ↔
      first γ = μ ∧ second γ = ν := by
  constructor
  · intro h
    exact ⟨ProbabilityMeasure.toMeasure_injective h.1,
      ProbabilityMeasure.toMeasure_injective h.2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨congrArg (fun x : ProbabilityMeasure X => (x : Measure X)) h1,
      congrArg (fun x : ProbabilityMeasure X => (x : Measure X)) h2⟩

lemma couplings_closed (μ ν : ProbabilityMeasure X) :
    IsClosed {γ : ProbabilityMeasure (X × X) |
      (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)} := by
  simp only [coupling_iff]
  exact (isClosed_eq first_continuous continuous_const).inter
    (isClosed_eq second_continuous continuous_const)

lemma joint_tight (S : Set (ProbabilityMeasure (X × X)))
    (h1 : IsTightMeasureSet ((fun γ => ((first γ : ProbabilityMeasure X) : Measure X)) '' S))
    (h2 : IsTightMeasureSet ((fun γ => ((second γ : ProbabilityMeasure X) : Measure X)) '' S)) :
    IsTightMeasureSet ((fun γ : ProbabilityMeasure (X × X) => (γ : Measure (X × X))) '' S) := by
  apply IsTightMeasureSet.prodMk
  · convert h1 using 1
    simp only [image_image]
    rfl
  · convert h2 using 1
    simp only [image_image]
    rfl

lemma couplings_compact [ProperSpace X] (μ ν : ProbabilityMeasure X) :
    IsCompact {γ : ProbabilityMeasure (X × X) |
      (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)} := by
  let S : Set (ProbabilityMeasure (X × X)) :=
    {γ | (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)}
  have ht : IsTightMeasureSet ((fun γ : ProbabilityMeasure (X × X) =>
      (γ : Measure (X × X))) '' S) := by
    apply joint_tight
    · apply (isTightMeasureSet_singleton (μ := (μ : Measure X))).subset
      rintro m ⟨γ,hγ,rfl⟩
      simp only [mem_singleton_iff]
      exact hγ.1
    · apply (isTightMeasureSet_singleton (μ := (ν : Measure X))).subset
      rintro m ⟨γ,hγ,rfl⟩
      simp only [mem_singleton_iff]
      exact hγ.2
  have hs : IsClosed S := couplings_closed μ ν
  simpa only [hs.closure_eq] using isCompact_closure_of_isTightMeasureSet ht

lemma integral_sublevel_closed [SeparableSpace X] (f : X → ℝ) (hf : Continuous f)
    (hfn : ∀ x, 0 ≤ f x) (C : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure X | ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) ≤ C} := by
  apply IsSeqClosed.isClosed
  intro μs μ hμs hlim
  have hi := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hfn (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
  exact hi.trans (liminf_le_of_frequently_le (Filter.Eventually.of_forall hμs).frequently)

end CouplingResearch

#print axioms CouplingResearch.couplings_compact
#print axioms CouplingResearch.integral_sublevel_closed

namespace CouplingResearch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

noncomputable def transportCost (p : ℝ) (γ : ProbabilityMeasure (X × X)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂(γ : Measure (X × X))

lemma transportCost_lsc [SeparableSpace X] (p : ℝ) (hp : 0 ≤ p) :
    LowerSemicontinuous (transportCost (X := X) p) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro C
  exact integral_sublevel_closed (fun z : X × X => dist z.1 z.2 ^ p)
    ((continuous_fst.dist continuous_snd).rpow_const (fun _ => Or.inr hp))
    (fun _ => Real.rpow_nonneg dist_nonneg _) C

lemma exists_coupling_cost_le [ProperSpace X] (p : ℝ) (hp : 0 ≤ p)
    (μ ν : ProbabilityMeasure X) (C : ℝ≥0∞)
    (hC : (⨅ κ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂κ) ≤ C) :
    ∃ γ : ProbabilityMeasure (X × X),
      (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X) ∧
      transportCost p γ ≤ C := by
  let S : Set (ProbabilityMeasure (X × X)) :=
    {γ | (γ : Measure (X × X)) ∈ couplings (μ : Measure X) (ν : Measure X)}
  have hne : S.Nonempty := by
    refine ⟨⟨(μ : Measure X).prod (ν : Measure X), inferInstance⟩, ?_⟩
    change ((μ : Measure X).prod (ν : Measure X)).map Prod.fst = (μ : Measure X) ∧
      ((μ : Measure X).prod (ν : Measure X)).map Prod.snd = (ν : Measure X)
    simp
  obtain ⟨γ,hγ,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne
    (couplings_compact μ ν) ((transportCost_lsc p hp).lowerSemicontinuousOn S)
  refine ⟨γ,hγ,le_trans ?_ hC⟩
  apply le_iInf
  intro κ
  apply le_iInf
  intro hκ
  haveI : IsProbabilityMeasure (κ.map Prod.fst) := hκ.1.symm ▸ μ.property
  haveI : IsProbabilityMeasure κ := Measure.isProbabilityMeasure_of_map Prod.fst
  exact (isMinOn_iff.mp hmin) ⟨κ,inferInstance⟩ hκ

lemma ball_representation [ProperSpace X] (p r : ℝ) (hp : 0 < p)
    (ν : ProbabilityMeasure X) :
    wassersteinBall p r ν = first ''
      {γ : ProbabilityMeasure (X × X) | second γ = ν ∧
        transportCost p γ ≤ (ENNReal.ofReal r) ^ p} := by
  ext μ
  constructor
  · intro hμ
    have hi : (⨅ κ ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂κ) ≤ (ENNReal.ofReal r) ^ p := by
      apply (ENNReal.rpow_inv_le_iff hp).mp
      simpa only [wassersteinBall, wassersteinDist, mem_setOf_eq, one_div] using hμ
    obtain ⟨γ,hγ,hcost⟩ := exists_coupling_cost_le p hp.le μ ν _ hi
    have hc := (coupling_iff γ μ ν).mp hγ
    exact ⟨γ,⟨hc.2,hcost⟩,hc.1⟩
  · rintro ⟨γ,⟨hsecond,hcost⟩,rfl⟩
    have hc := (coupling_iff γ (first γ) ν).mpr ⟨rfl,hsecond⟩
    change (⨅ κ ∈ couplings ((first γ : ProbabilityMeasure X) : Measure X)
      (ν : Measure X), ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂κ) ^ (1 / p)
      ≤ ENNReal.ofReal r
    rw [one_div]
    apply (ENNReal.rpow_inv_le_iff hp).mpr
    exact (iInf_le_of_le (γ : Measure (X × X)) (iInf_le_of_le hc le_rfl)).trans hcost

end CouplingResearch

#print axioms CouplingResearch.ball_representation

/-- Weak compactness of a positive-radius Wasserstein ball on a proper metric
space, for a center with finite p-th moment and p ≥ 1. -/
theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X)) :
    IsCompact (wassersteinBall p r ν) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let S : Set (ProbabilityMeasure (X × X)) :=
    {γ | CouplingResearch.second γ = ν ∧
      CouplingResearch.transportCost p γ ≤ (ENNReal.ofReal r) ^ p}
  have hrep : wassersteinBall p r ν = CouplingResearch.first '' S :=
    CouplingResearch.ball_representation p r hp0 ν
  have hs : IsClosed S :=
    (isClosed_eq CouplingResearch.second_continuous continuous_const).inter
      ((lowerSemicontinuous_iff_isClosed_preimage.mp
        (CouplingResearch.transportCost_lsc p hp0.le)) _)
  have htBall := (ReusedTightness.solution p r hp hr ν hν).1
  have ht : IsTightMeasureSet ((fun γ : ProbabilityMeasure (X × X) =>
      (γ : Measure (X × X))) '' S) := by
    apply CouplingResearch.joint_tight
    · apply htBall.subset
      rintro m ⟨γ,hγ,rfl⟩
      refine ⟨CouplingResearch.first γ, ?_, rfl⟩
      rw [hrep]
      exact ⟨γ,hγ,rfl⟩
    · apply (isTightMeasureSet_singleton (μ := (ν : Measure X))).subset
      rintro m ⟨γ,hγ,rfl⟩
      simp only [mem_singleton_iff]
      exact congrArg (fun μ : ProbabilityMeasure X => (μ : Measure X)) hγ.1
  have hc : IsCompact S := by
    simpa only [hs.closure_eq] using isCompact_closure_of_isTightMeasureSet ht
  rw [hrep]
  exact hc.image CouplingResearch.first_continuous

#print axioms solution
