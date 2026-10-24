-- Prove2me | solution 1 for WassersteinLinOpt.Ball.optimalValue_finite_iff_growth
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T09:31:07.425886+00:00
-- url     : https://prove2.me/submissions/12b9bd14-afd5-48b7-aca8-d291796b7e79

/-
Complete finiteness characterization, 23 October2026.
Original theorem: Yue, Kuhn and Wiesemann, On linear optimization over Wasserstein
balls, Theorem2. The converse here uses an explicit truncation coupling and small
Dirac mixtures. The accepted uniform-moment source and earlier checked sufficiency
are retained below. Alexander Richard Towell stewards the work; OpenAI Codex
constructed and checked this formalization. No novelty or human review claimed.
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
import Definitions.Def_WassersteinLinOpt_Ball_optimalValue
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_HasFinitePthMoment

open MeasureTheory
open scoped ENNReal NNReal

namespace AcceptedMoment

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

end AcceptedMoment
open MeasureTheory Filter Set
open scoped ENNReal NNReal
open WassersteinLinOpt.Ball

namespace FinitenessSupport

lemma bounded_objective_coupling {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 0 < p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : Measurable f) :
    ∃ μ ∈ wassersteinBall p r ν, ∃ γ ∈ couplings (μ : Measure X) (ν : Measure X),
      (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ) < (ENNReal.ofReal r)^p ∧
      (∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X)) ≠ ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X)) ≠ ⊤ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hν
  let T : ℕ → X → X := fun n x => if |f x| ≤ (n : ℝ) then x else x₀
  have hT : ∀ n, Measurable (T n) := fun n =>
    Measurable.ite (measurableSet_le hf.abs measurable_const) measurable_id measurable_const
  let C : ℕ → X → ℝ≥0∞ := fun n x => ENNReal.ofReal (dist (T n x) x ^ p)
  have hC : ∀ n, Measurable (C n) := by intro n; dsimp [C]; fun_prop
  have hbound : ∀ n, C n ≤ᵐ[(ν : Measure X)] (fun x => ENNReal.ofReal (dist x x₀ ^ p)) := by
    intro n
    filter_upwards [] with x
    dsimp [C,T]
    split_ifs
    · simp [Real.zero_rpow (ne_of_gt hp)]
    · rw [dist_comm]
  have hlim : ∀ᵐ x ∂(ν : Measure X), Tendsto (fun n => C n x) atTop (nhds 0) := by
    filter_upwards [] with x
    obtain ⟨N,hN⟩ := exists_nat_gt |f x|
    apply tendsto_congr' _ |>.2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : |f x| ≤ (n : ℝ) := le_trans hN.le hn'
    simp [C,T,hx,Real.zero_rpow (ne_of_gt hp)]
  have hint : Tendsto (fun n => ∫⁻ x, C n x ∂(ν : Measure X)) atTop (nhds 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (dist x x₀ ^ p)) hC hbound hx₀.ne hlim
  have hR : (0 : ℝ≥0∞) < (ENNReal.ofReal r)^p := ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hint).2 _ hR).exists
  let μ : ProbabilityMeasure X := ν.map (hT n).aemeasurable
  let γ : Measure (X × X) := (ν : Measure X).map (fun x => (T n x,x))
  have hpair : Measurable (fun x => (T n x,x)) := (hT n).prodMk measurable_id
  have hγ : γ ∈ couplings (μ : Measure X) (ν : Measure X) := by
    constructor
    · rw [Measure.map_map measurable_fst hpair]
      rfl
    · rw [Measure.map_map measurable_snd hpair]
      simp [Function.comp_def]
  have hcost : (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ) = ∫⁻ x, C n x ∂(ν : Measure X) := by
    rw [lintegral_map (by fun_prop) hpair]
  have hμ : μ ∈ wassersteinBall p r ν := by
    change (⨅ η ∈ couplings (μ : Measure X) (ν : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂η) ^ (1/p) ≤ ENNReal.ofReal r
    rw [one_div,ENNReal.rpow_inv_le_iff hp]
    exact (iInf_le_of_le γ (iInf_le_of_le hγ (le_refl _))).trans (hcost.trans_le hn.le)
  refine ⟨μ,hμ,γ,hγ,hcost.trans_lt hn,?_,?_⟩
  all_goals
    change (∫⁻ x, _ ∂(ν : Measure X).map (T n)) ≠ ⊤
    rw [lintegral_map (by fun_prop) (hT n)]
    apply ne_top_of_le_ne_top (show ENNReal.ofReal ((n : ℝ) + |f x₀|) ≠ ⊤ from ENNReal.ofReal_ne_top)
    calc
      _ ≤ ∫⁻ _x : X, ENNReal.ofReal ((n : ℝ) + |f x₀|) ∂(ν : Measure X) := by
        apply lintegral_mono
        intro x
        apply ENNReal.ofReal_le_ofReal
        dsimp [T]
        split_ifs with h
        · have hab := abs_le.mp h
          have hz := abs_nonneg (f x₀)
          linarith
        · have ha := le_abs_self (f x₀)
          have hb := neg_le_abs (f x₀)
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
      _ = _ := by simp

lemma bounded_objective_measure {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 0 < p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : Measurable f) :
    ∃ μ ∈ wassersteinBall p r ν,
      (∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X)) ≠ ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X)) ≠ ⊤ := by
  obtain ⟨μ,hμ,γ,hγ,hcost,hpos,hneg⟩ := bounded_objective_coupling p r hp hr ν hν f hf
  exact ⟨μ,hμ,hpos,hneg⟩

lemma positive_part_bound {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (x₀ : X) (c : ℝ) (hc : 0 < c)
    (hgrowth : ∀ x, f x ≤ c*(1+dist x x₀^p)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) ≤ ENNReal.ofReal B := by
  obtain ⟨M,hM,hbound⟩ := AcceptedMoment.solution p r hp hr ν hν x₀
  refine ⟨c+c*M,by positivity,?_⟩
  intro μ hμ
  have hm : Measurable (fun x : X => ENNReal.ofReal (dist x x₀^p)) := by fun_prop
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (c+c*(dist x x₀^p)) ∂(μ : Measure X) := by
      apply lintegral_mono; intro x; apply ENNReal.ofReal_le_ofReal
      nlinarith [hgrowth x]
    _ = ENNReal.ofReal c + ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (dist x x₀^p) ∂(μ : Measure X) := by
      simp_rw [ENNReal.ofReal_add hc.le (mul_nonneg hc.le (Real.rpow_nonneg dist_nonneg _)),ENNReal.ofReal_mul hc.le]
      rw [lintegral_add_left measurable_const,lintegral_const_mul _ hm]
      simp
    _ ≤ ENNReal.ofReal c + ENNReal.ofReal c * ENNReal.ofReal M := by gcongr; exact hbound μ hμ
    _ = _ := by rw [ENNReal.ofReal_add hc.le (mul_nonneg hc.le hM.le),ENNReal.ofReal_mul hc.le]

end FinitenessSupport

namespace FinitenessSupport

lemma optimalValue_ne_bot {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 0 < p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : Measurable f) : optimalValue p r ν f ≠ ⊥ := by
  obtain ⟨μ,hμ,hpos,hneg⟩ := bounded_objective_measure p r hp hr ν hν f hf
  have hfin : quasiIntegral f (μ : Measure X) ≠ ⊥ := by
    unfold quasiIntegral
    rw [← EReal.coe_ennreal_toReal hpos,← EReal.coe_ennreal_toReal hneg,← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  apply ne_bot_of_le_ne_bot hfin
  exact le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)

lemma growth_upper {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (x₀ : X) (c : ℝ) (hc : 0 < c)
    (hgrowth : ∀ x, f x ≤ c*(1+dist x x₀^p)) : optimalValue p r ν f ≠ ⊤ := by
  obtain ⟨B,hB,hbound⟩ := positive_part_bound p r hp hr ν hν f x₀ c hc hgrowth
  have hupper : optimalValue p r ν f ≤ (B : EReal) := by
    apply iSup_le; intro μ; apply iSup_le; intro hμ
    have hpos : ((∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) : ℝ≥0∞) : EReal) ≤ (B : EReal) := by
      have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hbound μ hμ)
      simpa [EReal.coe_ennreal_ofReal,hB] using hh
    have hs := EReal.sub_le_sub hpos (EReal.coe_ennreal_nonneg (∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X)))
    simpa only [quasiIntegral,sub_zero] using hs
  exact ne_top_of_le_ne_top (EReal.coe_ne_top B) hupper

end FinitenessSupport

theorem sufficiency {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤) :
    (∃ x₀ : X, ∃ c : ℝ, 0 < c ∧ ∀ x : X, f x ≤ c*(1+dist x x₀^p)) →
      (optimalValue p r ν f ≠ ⊤ ∧ optimalValue p r ν f ≠ ⊥) := by
  rintro ⟨x₀,c,hc,hgrowth⟩
  exact ⟨FinitenessSupport.growth_upper p r hp hr ν hν f x₀ c hc hgrowth,
    FinitenessSupport.optimalValue_ne_bot p r (lt_of_lt_of_le zero_lt_one hp) hr ν hν f hf.measurable⟩

open MeasureTheory Filter Set
open scoped ENNReal NNReal
open WassersteinLinOpt.Ball

namespace FinitenessNecessity

lemma quasi_mix {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (x : X) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : (∫⁻ y, ENNReal.ofReal (f y) ∂μ) ≠ ⊤)
    (hneg : (∫⁻ y, ENNReal.ofReal (-f y) ∂μ) ≠ ⊤) :
    quasiIntegral f (ENNReal.ofReal a • μ + ENNReal.ofReal b • Measure.dirac x) =
      ((a * ((∫⁻ y, ENNReal.ofReal (f y) ∂μ).toReal -
         (∫⁻ y, ENNReal.ofReal (-f y) ∂μ).toReal) + b*f x : ℝ) : EReal) := by
  have hparts (g : X → ℝ) :
      (∫⁻ y, ENNReal.ofReal (g y) ∂(ENNReal.ofReal a • μ + ENNReal.ofReal b • Measure.dirac x)) =
      ENNReal.ofReal a * (∫⁻ y, ENNReal.ofReal (g y) ∂μ) + ENNReal.ofReal b * ENNReal.ofReal (g x) := by
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac]
    rfl
  have hfinite (g : X → ℝ) (hg : (∫⁻ y, ENNReal.ofReal (g y) ∂μ) ≠ ⊤) :
      ENNReal.ofReal a * (∫⁻ y, ENNReal.ofReal (g y) ∂μ) + ENNReal.ofReal b * ENNReal.ofReal (g x) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  unfold quasiIntegral
  rw [hparts f,hparts (fun y => -f y)]
  rw [← EReal.coe_ennreal_toReal (hfinite f hpos),← EReal.coe_ennreal_toReal (hfinite (fun y => -f y) hneg),← EReal.coe_sub]
  congr 1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpos) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hneg) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal']
  rcases le_total 0 (f x) with hx | hx
  · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [max_eq_right hx,max_eq_left (neg_nonneg.mpr hx)]
    ring

lemma point_coupling {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : ProbabilityMeasure X) (x : X) :
    (ν : Measure X).map (fun y => (x,y)) ∈ couplings (Measure.dirac x) (ν : Measure X) := by
  have hpair : Measurable (fun y : X => (x,y)) := measurable_const.prodMk measurable_id
  constructor
  · rw [Measure.map_map measurable_fst hpair]
    simp only [Function.comp_def]
    simp
  · rw [Measure.map_map measurable_snd hpair]
    simp [Function.comp_def]

lemma mixed_coupling {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : ProbabilityMeasure X) (μ : Measure X)
    (γ : Measure (X × X)) (hγ : γ ∈ couplings μ (ν : Measure X))
    (x : X) (a b : ℝ≥0∞) (hab : a+b=1) :
    a • γ + b • (ν : Measure X).map (fun y => (x,y)) ∈
      couplings (a • μ + b • Measure.dirac x) (ν : Measure X) := by
  have hx := point_coupling ν x
  constructor
  · simp only [Measure.map_add _ _ measurable_fst,Measure.map_smul,hγ.1,hx.1]
  · simp only [Measure.map_add _ _ measurable_snd,Measure.map_smul,hγ.2,hx.2]
    rw [← add_smul,hab,one_smul]

end FinitenessNecessity

open MeasureTheory Filter Set
open scoped ENNReal NNReal
open WassersteinLinOpt.Ball
open AcceptedMoment.WassersteinMomentProof
namespace FinitenessNecessity

lemma point_cost_bound {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (p : ℝ) (hp : 0 ≤ p) (ν : ProbabilityMeasure X)
    (hν : HasFinitePthMoment p (ν : Measure X)) :
    ∃ x₀ : X, ∃ K : ℝ, 0 < K ∧ ∀ x : X,
      (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂((ν : Measure X).map (fun y => (x,y)))) ≤
        ENNReal.ofReal (K*(1+dist x x₀^p)) := by
  obtain ⟨x₀,hx₀⟩ := hν
  let M := ∫⁻ y, ENNReal.ofReal (dist y x₀^p) ∂(ν : Measure X)
  have hM : M ≠ ⊤ := hx₀.ne
  have hK : 0 < (2 : ℝ)^p * (M.toReal+1) := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by positivity)
  refine ⟨x₀,2^p*(M.toReal+1),hK,?_⟩
  intro x
  have he : (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂((ν : Measure X).map (fun y => (x,y)))) = moment p (ν : Measure X) x := by
    have hmap : Measurable (fun y : X => (x,y)) := measurable_const.prodMk measurable_id
    have hfun : Measurable (fun z : X × X => ENNReal.ofReal (dist z.1 z.2 ^ p)) := by fun_prop
    rw [lintegral_map hfun hmap]
    simp only [moment,cost,dist_comm x,ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp]
  rw [he]
  calc
    moment p (ν : Measure X) x ≤ (2 : ℝ≥0∞)^p * (moment p (ν : Measure X) x₀ + cost p x₀ x) := moment_change p hp ν x₀ x
    _ = ENNReal.ofReal ((2 : ℝ)^p * (M.toReal + dist x x₀^p)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),ENNReal.ofReal_add ENNReal.toReal_nonneg (Real.rpow_nonneg dist_nonneg _),ENNReal.ofReal_toReal hM]
      simp only [moment,cost,dist_comm x₀,ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp]
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp]
      norm_num
      rfl
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h2 : 0 ≤ (2 : ℝ)^p := Real.rpow_nonneg (by norm_num) _
      have hm : 0 ≤ M.toReal := ENNReal.toReal_nonneg
      have hd : 0 ≤ dist x x₀^p := Real.rpow_nonneg dist_nonneg _
      calc
        _ ≤ 2^p*((M.toReal+1)*(1+dist x x₀^p)) := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hm hd]) h2
        _ = _ := by ring

end FinitenessNecessity

open MeasureTheory Filter Set
open scoped ENNReal NNReal
open WassersteinLinOpt.Ball
namespace FinitenessNecessity

lemma feasible_mixtures {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 0 < p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : Measurable f) :
    ∃ x₀ : X, ∃ a J : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ x : X,
      ∃ μ ∈ wassersteinBall p r ν,
        quasiIntegral f (μ : Measure X) =
          (((1-a/(1+dist x x₀^p))*J + (a/(1+dist x x₀^p))*f x : ℝ) : EReal) := by
  obtain ⟨μ₀,hμ₀,γ₀,hγ₀,hcost,hpos,hneg⟩ := FinitenessSupport.bounded_objective_coupling p r hp hr ν hν f hf
  obtain ⟨x₀,K,hK,hpoint⟩ := point_cost_bound p hp.le ν hν
  let I := ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ₀
  let R : ℝ := r^p
  have hR : 0 < R := Real.rpow_pos_of_pos hr _
  have hRpow : ENNReal.ofReal R = (ENNReal.ofReal r)^p := (ENNReal.ofReal_rpow_of_nonneg hr.le hp.le).symm
  have hI : I ≠ ⊤ := ne_top_of_lt (hcost.trans_le le_top)
  have hIR : I.toReal < R := by
    have h := (ENNReal.toReal_lt_toReal hI ENNReal.ofReal_ne_top).mpr (hcost.trans_eq hRpow.symm)
    simpa only [ENNReal.toReal_ofReal hR.le] using h
  let a := min 1 ((R-I.toReal)/(K+1))
  have ha : 0 < a := lt_min (by norm_num) (div_pos (sub_pos.mpr hIR) (by linarith))
  have ha1 : a ≤ 1 := min_le_left _ _
  have haK : a*K ≤ R-I.toReal := by
    have hh : a*(K+1) ≤ R-I.toReal := (le_div_iff₀ (by linarith : 0<K+1)).mp (min_le_right _ _)
    nlinarith
  let J := (∫⁻ y, ENNReal.ofReal (f y) ∂(μ₀ : Measure X)).toReal -
    (∫⁻ y, ENNReal.ofReal (-f y) ∂(μ₀ : Measure X)).toReal
  refine ⟨x₀,a,J,ha,ha1,?_⟩
  intro x
  let D : ℝ := 1+dist x x₀^p
  have hD : 1 ≤ D := by dsimp [D]; exact le_add_of_nonneg_right (Real.rpow_nonneg dist_nonneg _)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let t := a/D
  have ht : 0 ≤ t := (div_pos ha hDpos).le
  have ht1 : t ≤ 1 := (div_le_one hDpos).mpr (ha1.trans hD)
  have h1t : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hweights : ENNReal.ofReal (1-t)+ENNReal.ofReal t=1 := by
    rw [← ENNReal.ofReal_add h1t ht]
    simp
  let μ : ProbabilityMeasure X := ⟨ENNReal.ofReal (1-t) • (μ₀ : Measure X) + ENNReal.ofReal t • Measure.dirac x,
    isProbabilityMeasure_iff.mpr (by simpa using hweights)⟩
  let γ : Measure (X × X) := ENNReal.ofReal (1-t) • γ₀ + ENNReal.ofReal t • (ν : Measure X).map (fun y => (x,y))
  have hγ : γ ∈ couplings (μ : Measure X) (ν : Measure X) := mixed_coupling ν (μ₀ : Measure X) γ₀ hγ₀ x _ _ hweights
  have hmult : t * (K*D) = a*K := by dsimp [t]; field_simp <;> ring
  have htotal : (1-t)*I.toReal + t*(K*D) ≤ R := by
    rw [hmult]
    have hprod : 0 ≤ t*I.toReal := mul_nonneg ht ENNReal.toReal_nonneg
    nlinarith
  have hγcost : (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ) ≤ (ENNReal.ofReal r)^p := by
    change (∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂(ENNReal.ofReal (1-t) • γ₀ + ENNReal.ofReal t • (ν : Measure X).map (fun y => (x,y)))) ≤ _
    rw [lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure]
    change ENNReal.ofReal (1-t)*I + ENNReal.ofReal t * _ ≤ _
    calc
      _ ≤ ENNReal.ofReal (1-t)*I + ENNReal.ofReal t * ENNReal.ofReal (K*D) := by gcongr; exact hpoint x
      _ = ENNReal.ofReal ((1-t)*I.toReal+t*(K*D)) := by
        rw [ENNReal.ofReal_add (mul_nonneg h1t ENNReal.toReal_nonneg) (mul_nonneg ht (mul_nonneg hK.le hDpos.le)),
          ENNReal.ofReal_mul h1t,ENNReal.ofReal_mul ht,ENNReal.ofReal_toReal hI]
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal htotal
      _ = _ := hRpow
  refine ⟨μ,?_,?_⟩
  · change (⨅ η ∈ couplings (μ : Measure X) (ν : Measure X),
        ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂η) ^ (1/p) ≤ ENNReal.ofReal r
    rw [one_div,ENNReal.rpow_inv_le_iff hp]
    exact (iInf_le_of_le γ (iInf_le_of_le hγ (le_refl _))).trans hγcost
  · exact quasi_mix (μ₀ : Measure X) f x (1-t) t h1t ht hpos hneg

lemma necessity {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 0 < p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : Measurable f)
    (hfin : optimalValue p r ν f ≠ ⊤ ∧ optimalValue p r ν f ≠ ⊥) :
    ∃ x₀ : X, ∃ c : ℝ, 0 < c ∧ ∀ x : X, f x ≤ c*(1+dist x x₀^p) := by
  obtain ⟨x₀,a,J,ha,ha1,hmix⟩ := feasible_mixtures p r hp hr ν hν f hf
  let V := (optimalValue p r ν f).toReal
  let c := (|V|+|J|+1)/a
  have hc : 0<c := div_pos (by positivity) ha
  refine ⟨x₀,c,hc,?_⟩
  intro x
  let D := 1+dist x x₀^p
  have hD : 1 ≤ D := by dsimp [D]; exact le_add_of_nonneg_right (Real.rpow_nonneg dist_nonneg _)
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ht : 0 ≤ a/D := (div_pos ha hDp).le
  have ht1 : a/D ≤ 1 := (div_le_one hDp).mpr (ha1.trans hD)
  obtain ⟨μ,hμ,heq⟩ := hmix x
  have hle : quasiIntegral f (μ : Measure X) ≤ optimalValue p r ν f := le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)
  rw [heq,← EReal.coe_toReal hfin.1 hfin.2,EReal.coe_le_coe_iff] at hle
  have hJ : -|J| ≤ (1-a/D)*J := by
    rcases le_total 0 J with hJ | hJ
    · exact (neg_nonpos.mpr (abs_nonneg J)).trans (mul_nonneg (sub_nonneg.mpr ht1) hJ)
    · rw [abs_of_nonpos hJ]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hJ]
  have hab : (a/D)*f x ≤ |V|+|J|+1 := by
    have hV := le_abs_self V
    change (1-a/D)*J+(a/D)*f x ≤ V at hle
    linarith
  have hfx : f x ≤ (|V|+|J|+1)/(a/D) := (le_div_iff₀ (div_pos ha hDp)).mpr (by simpa [mul_comm] using hab)
  calc
    f x ≤ (|V|+|J|+1)/(a/D) := hfx
    _ = c*(1+dist x x₀^p) := by dsimp [c,D]; field_simp <;> ring

end FinitenessNecessity

/-- Complete exact finiteness equivalence; new converse by explicit feasible mixtures. -/
theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r)
    (ν : ProbabilityMeasure X) (hν : HasFinitePthMoment p (ν : Measure X))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤) :
    (optimalValue p r ν f ≠ ⊤ ∧ optimalValue p r ν f ≠ ⊥) ↔
      ∃ x₀ : X, ∃ c : ℝ, 0 < c ∧ ∀ x : X, f x ≤ c * (1 + dist x x₀ ^ p) := by
  constructor
  · exact FinitenessNecessity.necessity p r (lt_of_lt_of_le zero_lt_one hp) hr ν hν f hf.measurable
  · exact sufficiency p r hp hr ν hν f hf hquasi
