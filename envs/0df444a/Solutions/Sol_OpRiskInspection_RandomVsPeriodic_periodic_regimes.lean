-- Prove2me | solution 1 for OpRiskInspection.RandomVsPeriodic.periodic_regimes
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:56:47.787836+00:00
-- url     : https://prove2.me/submissions/acd46597-bba8-47c8-a7c3-671f121e62e9

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_ClosedForms

open MeasureTheory Set Real

namespace OpInspCore

lemma int_expMeasure (v : ℝ) (hv : 0 < v) (f : ℝ → ℝ) :
    ∫ τ, f τ ∂(ProbabilityTheory.expMeasure v) = ∫ τ in Ioi 0, v * exp (-(v*τ)) * f τ := by
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (ProbabilityTheory.gammaPDF 1 v) from
      (ProbabilityTheory.measurable_gammaPDFReal 1 v).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  funext x
  simp only [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal, smul_eq_mul,
    Set.indicator, mem_Ici]
  split_ifs with h
  · rw [ENNReal.toReal_ofReal (by positivity)]
    simp [Real.Gamma_one]
  · simp

lemma tail_exp (k t : ℝ) (hk : 0 < k) : ∫ τ in Ioi t, k * exp (-(k*τ)) = exp (-(k*t)) := by
  rw [integral_const_mul]
  have := integral_exp_mul_Ioi (a := -k) (by linarith) t
  simp only [neg_mul] at this
  rw [this]; field_simp

lemma lemA_bdd (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ t, |g t| ≤ B) (k : ℝ)
    (hk : 0 < k) :
    ∫ τ in Ioi 0, k * exp (-(k*τ)) * (∫ t in (0)..τ, g t) =
      ∫ t in Ioi 0, g t * exp (-(k*t)) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  set F : ℝ → ℝ → ℝ := fun τ t => k * exp (-(k*τ)) * (if t ≤ τ then g t else 0) with hF
  have h1 : ∀ τ ∈ Ioi (0:ℝ), k * exp (-(k*τ)) * (∫ t in (0)..τ, g t) =
      ∫ t in Ioi 0, F τ t := by
    intro τ hτ
    simp only [hF]
    rw [integral_const_mul, intervalIntegral.integral_of_le (le_of_lt hτ)]
    congr 1
    have : (fun t => if t ≤ τ then g t else 0) = (Iic τ).indicator g := by
      funext t; simp [Set.indicator, mem_Iic]
    rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]
  rw [setIntegral_congr_fun measurableSet_Ioi h1]
  have hmeas : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
    · exact (measurable_fst.const_mul k).neg.exp
    · exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hg.comp measurable_snd) measurable_const
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hf1 : Integrable (fun τ : ℝ => B * k * exp (-(k/2) * τ)) (volume.restrict (Ioi 0)) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < k/2)).const_mul (B*k)
    have hf2 : Integrable (fun t : ℝ => exp (-(k/2) * t)) (volume.restrict (Ioi 0)) :=
      exp_neg_integrableOn_Ioi 0 (by linarith : 0 < k/2)
    refine Integrable.mono' (hf1.mul_prod hf2) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    simp only [hF, Function.uncurry_def, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_mul, abs_mul, abs_of_pos hk, abs_of_pos (exp_pos _)]
      have he : exp (-(k*z.1)) ≤ exp (-(k/2) * z.1) * exp (-(k/2) * z.2) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have := hB z.2
      calc k * exp (-(k*z.1)) * |g z.2| ≤ k * (exp (-(k/2) * z.1) * exp (-(k/2) * z.2)) * B := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left he hk.le) this (abs_nonneg _)
            positivity
        _ = B * k * exp (-(k/2) * z.1) * exp (-(k/2) * z.2) := by ring
    · simp; positivity
  rw [integral_integral_swap hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [hF]
  have : (fun τ => k * exp (-(k*τ)) * (if t ≤ τ then g t else 0)) =
      (Ici t).indicator (fun τ => k * exp (-(k*τ)) * g t) := by
    funext τ; simp [Set.indicator, mem_Ici]
  rw [this, setIntegral_indicator measurableSet_Ici]
  have hs : Ioi (0:ℝ) ∩ Ici t = Ici t := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
    · exact fun h => h.2
    · intro h; exact ⟨lt_of_lt_of_le (mem_Ioi.mp ht) h, h⟩
  rw [hs, integral_Ici_eq_integral_Ioi, integral_mul_const, tail_exp k t hk]
  ring

lemma lemA (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ t, 0 < t → |g t| ≤ B) (k : ℝ)
    (hk : 0 < k) :
    ∫ τ in Ioi 0, k * exp (-(k*τ)) * (∫ t in (0)..τ, g t) =
      ∫ t in Ioi 0, g t * exp (-(k*t)) := by
  set g' : ℝ → ℝ := fun t => if 0 < t then g t else 0 with hg'
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 1 one_pos)
  have key := lemA_bdd g' (Measurable.ite measurableSet_Ioi hg measurable_const) B
    (by intro t; simp only [hg']; split_ifs with h
        · exact hB t h
        · simp [hB0]) k hk
  have e1 : ∫ τ in Ioi 0, k * exp (-(k*τ)) * (∫ t in (0)..τ, g t) =
      ∫ τ in Ioi 0, k * exp (-(k*τ)) * (∫ t in (0)..τ, g' t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro τ hτ
    simp only
    congr 1
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le (le_of_lt hτ)] at hx
    simp [hg', hx.1]
  have e2 : ∫ t in Ioi 0, g t * exp (-(k*t)) = ∫ t in Ioi 0, g' t * exp (-(k*t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht; simp [hg', mem_Ioi.mp ht]
  rw [e1, e2, key]

section Random
open OpRiskInspection.RandomVsPeriodic

lemma exp_neg_le_one' (a : Effort) (ha0 : ∀ t, 0 ≤ a t) (s : ℝ) : exp (-(a s)) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith [ha0 s]

lemma ii_expneg (a : Effort) (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) (x y : ℝ) :
    IntervalIntegrable (fun s => exp (-(a s))) volume x y := by
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun ?_ ?_
  · exact (ha.neg.exp).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun s => ?_)
    simp only [Real.norm_eq_abs, abs_of_pos (exp_pos _), abs_one]
    exact exp_neg_le_one' a ha0 s

lemma expCount_bounds (p : Params) (hlam : 0 < p.lam) (a : Effort) (ha : Measurable a)
    (ha0 : ∀ t, 0 ≤ a t) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ expCount p a t ∧ expCount p a t ≤ p.lam * t := by
  unfold expCount
  constructor
  · apply mul_nonneg hlam.le
    exact intervalIntegral.integral_nonneg ht (fun s _ => (exp_pos _).le)
  · apply mul_le_mul_of_nonneg_left _ hlam.le
    have := intervalIntegral.integral_mono_on ht (ii_expneg a ha ha0 0 t)
      (intervalIntegrable_const (c := (1:ℝ))) (fun s _ => exp_neg_le_one' a ha0 s)
    simpa using this

lemma expCount_meas (p : Params) (a : Effort) (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) :
    Measurable (expCount p a) := by
  unfold expCount
  exact (continuous_const.mul
    (intervalIntegral.continuous_primitive (ii_expneg a ha ha0) 0)).measurable

lemma discF_random (p : Params) (hr : 0 < p.r) (v : ℝ) (hv : 0 < v) :
    discF p (randomLaw v) = v / (v + p.r) := by
  unfold discF randomLaw
  rw [int_expMeasure v hv]
  have h := tail_exp (v + p.r) 0 (by linarith)
  have e : ∀ τ : ℝ, v * exp (-(v*τ)) * exp (-(p.r * τ)) =
      v / (v + p.r) * ((v + p.r) * exp (-((v + p.r) * τ))) := by
    intro τ
    rw [show -((v + p.r) * τ) = -(v*τ) + -(p.r*τ) by ring, Real.exp_add]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, h]; simp

lemma effortInt_random (p : Params) (hr : 0 < p.r) (v : ℝ) (hv : 0 < v) (a : Effort)
    (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) (B : ℝ) (hB : ∀ t, a t ≤ B) :
    effortInt p (randomLaw v) a = ∫ t in Ioi 0, a t * exp (-((v + p.r) * t)) := by
  unfold effortInt randomLaw
  rw [int_expMeasure v hv]
  rw [lemA (fun t => a t * exp (-(p.r * t))) (ha.mul (measurable_const.mul measurable_id).neg.exp)
    B ?_ v hv]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only
    rw [show -((v + p.r) * t) = -(p.r*t) + -(v*t) by ring, Real.exp_add]; ring
  · intro t ht
    rw [abs_of_nonneg (mul_nonneg (ha0 t) (exp_pos _).le)]
    have : exp (-(p.r * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith [ha0 t, hB t, exp_pos (-(p.r * t))]

lemma Q_eq (p : Params) (v : ℝ) (hv : 0 < v) (hr : 0 < p.r) (a : Effort) (ha : Measurable a)
    (ha0 : ∀ t, 0 ≤ a t) :
    ∫ τ in Ioi 0, (v + p.r) * exp (-((v + p.r)*τ)) * (∫ t in (0)..τ, exp (-(a t))) =
      ∫ t in Ioi 0, exp (-(a t)) * exp (-((v + p.r) * t)) :=
  lemA (fun t => exp (-(a t))) ha.neg.exp 1 (fun t _ => by
    rw [abs_of_pos (exp_pos _)]; exact exp_neg_le_one' a ha0 t) (v + p.r) (by linarith)

lemma penaltyInt_random (p : Params) (hr : 0 < p.r) (v : ℝ) (hv : 0 < v) (a : Effort)
    (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) :
    penaltyInt p (randomLaw v) a =
      p.lam * v / (v + p.r) * ∫ t in Ioi 0, exp (-(a t)) * exp (-((v + p.r) * t)) := by
  unfold penaltyInt randomLaw
  rw [int_expMeasure v hv, ← Q_eq p v hv hr a ha ha0, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ _
  simp only [expCount]
  rw [show -((v + p.r) * τ) = -(v*τ) + -(p.r*τ) by ring, Real.exp_add]
  field_simp

lemma lossInt_random (p : Params) (hr : 0 < p.r) (hlam : 0 < p.lam) (v : ℝ) (hv : 0 < v)
    (a : Effort) (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) :
    lossInt p (randomLaw v) a =
      p.lam / (v + p.r) * ∫ t in Ioi 0, exp (-(a t)) * exp (-((v + p.r) * t)) := by
  unfold lossInt randomLaw
  rw [int_expMeasure v hv]
  rw [lemA (fun t => expCount p a t * exp (-(p.r * t)))
    ((expCount_meas p a ha ha0).mul (measurable_const.mul measurable_id).neg.exp)
    (p.lam / p.r) ?_ v hv]
  · rw [← Q_eq p v hv hr a ha ha0, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro τ _
    simp only [expCount]
    rw [show -((v + p.r) * τ) = -(v*τ) + -(p.r*τ) by ring, Real.exp_add]
    field_simp
  · intro t ht
    obtain ⟨h0, h1⟩ := expCount_bounds p hlam a ha ha0 t (le_of_lt ht)
    rw [abs_of_nonneg (mul_nonneg h0 (exp_pos _).le)]
    have hle : p.r * t + 1 ≤ exp (p.r * t) := by
      have := Real.add_one_le_exp (p.r * t); linarith
    have hpos : 0 < exp (p.r * t) := exp_pos _
    have he : exp (-(p.r * t)) = 1 / exp (p.r * t) := by rw [Real.exp_neg]; ring
    rw [he, le_div_iff₀ hr]
    rw [mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
end Random

section RandomOpt
open OpRiskInspection.RandomVsPeriodic

lemma pointwise_strict (c M x₀ : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hx : (0 < x₀ ∧ M * exp (-x₀) = c) ∨ (x₀ = 0 ∧ M ≤ c)) (x : ℝ) (hx0 : 0 ≤ x)
    (hne : x ≠ x₀) : c*x₀ + M*exp (-x₀) < c*x + M*exp (-x) := by
  rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hMpos : 0 < M := by
      by_contra h; push Not at h
      have : M = 0 := le_antisymm h hM
      rw [this] at h1; linarith
    have hlt : -(x - x₀) + 1 < exp (-(x - x₀)) := Real.add_one_lt_exp (by
      intro h; apply hne; linarith)
    have he : exp (-x) = exp (-x₀) * exp (-(x - x₀)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have hpos : 0 < M * exp (-x₀) := mul_pos hMpos (exp_pos _)
    have := mul_lt_mul_of_pos_left hlt hpos
    nlinarith
  · subst h0
    have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
    have hlt : -x + 1 < exp (-x) := Real.add_one_lt_exp (by linarith)
    simp only [mul_zero, neg_zero, Real.exp_zero, zero_add, mul_one]
    by_cases hMc : M = c
    · subst hMc
      nlinarith [mul_lt_mul_of_pos_left hlt hc]
    · have : M < c := lt_of_le_of_ne h1 hMc
      nlinarith [mul_le_mul_of_nonneg_left hlt.le hM]

lemma pointwise_le (c M x₀ : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hx : (0 < x₀ ∧ M * exp (-x₀) = c) ∨ (x₀ = 0 ∧ M ≤ c)) (x : ℝ) (hx0 : 0 ≤ x) :
    c*x₀ + M*exp (-x₀) ≤ c*x + M*exp (-x) := by
  by_cases h : x = x₀
  · rw [h]
  · exact (pointwise_strict c M x₀ hc hM hx x hx0 h).le

lemma intOn_bdd_exp (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ t, |g t| ≤ B) (k : ℝ)
    (hk : 0 < k) : IntegrableOn (fun t => g t * exp (-(k*t))) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => B * exp (-k * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hk).const_mul B
  refine Integrable.mono' hi ?_ ?_
  · exact (hg.mul ((measurable_const.mul measurable_id).neg.exp)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), neg_mul]
    exact mul_le_mul_of_nonneg_right (hB t) (exp_pos _).le

lemma agent_random (p : Params) (hp : Standing p) (v : ℝ) (hv : 0 < v) (P : ℝ)
    (a : Effort) (ha : Admissible a) :
    agentPayoff p (randomLaw v) a P 0 =
      -((v + p.r) / p.r) * ∫ t in Ioi 0,
        (p.c * a t + (P * p.lam * v / (v + p.r)) * exp (-(a t))) * exp (-((v + p.r) * t)) := by
  obtain ⟨ham, ha0, B, hB⟩ := ha
  have hr := hp.hr
  unfold agentPayoff
  rw [discF_random p hr v hv, effortInt_random p hr v hv a ham ha0 B hB,
    penaltyInt_random p hr v hv a ham ha0]
  have hk : 0 < v + p.r := by linarith
  have i1 := intOn_bdd_exp a ham B (fun t => by rw [abs_of_nonneg (ha0 t)]; exact hB t)
    (v + p.r) hk
  have i2 := intOn_bdd_exp (fun t => exp (-(a t))) ham.neg.exp 1
    (fun t => by rw [abs_of_pos (exp_pos _)]; exact exp_neg_le_one' a ha0 t) (v + p.r) hk
  have e : ∫ t in Ioi 0,
        (p.c * a t + (P * p.lam * v / (v + p.r)) * exp (-(a t))) * exp (-((v + p.r) * t)) =
      p.c * (∫ t in Ioi 0, a t * exp (-((v + p.r) * t))) +
      (P * p.lam * v / (v + p.r)) * ∫ t in Ioi 0, exp (-(a t)) * exp (-((v + p.r) * t)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
      (i2.const_mul _)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; simp only; ring
  rw [e]
  have h1 : 1 - v / (v + p.r) = p.r / (v + p.r) := by field_simp; ring
  rw [h1]
  field_simp
  ring

lemma admissible_const (x₀ : ℝ) (hx : 0 ≤ x₀) : Admissible (fun _ => x₀) :=
  ⟨measurable_const, fun _ => hx, x₀, fun _ => le_rfl⟩

lemma random_opt (p : Params) (hp : Standing p) (v : ℝ) (hv : 0 < v) (P : ℝ) (hP : 0 ≤ P)
    (x₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hx : (0 < x₀ ∧ (P * p.lam * v / (v + p.r)) * exp (-x₀) = p.c) ∨
      (x₀ = 0 ∧ (P * p.lam * v / (v + p.r)) ≤ p.c)) :
    AgentOptimal p (randomLaw v) P (fun _ => x₀) ∧
      ∀ a, AgentOptimal p (randomLaw v) P a →
        ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))), a t = x₀ := by
  have hr := hp.hr
  have hk : 0 < v + p.r := by linarith
  have hkr : 0 < (v + p.r) / p.r := div_pos hk hr
  set M := P * p.lam * v / (v + p.r) with hM
  have hM0 : 0 ≤ M := by
    have := hp.hlam; positivity
  -- integrability of the objective for an admissible effort
  have hint : ∀ a : Effort, Admissible a → IntegrableOn
      (fun t => (p.c * a t + M * exp (-(a t))) * exp (-((v + p.r) * t))) (Ioi 0) := by
    intro a ha
    obtain ⟨ham, ha0, B, hB⟩ := ha
    refine intOn_bdd_exp (fun t => p.c * a t + M * exp (-(a t)))
      ((measurable_const.mul ham).add (measurable_const.mul ham.neg.exp)) (p.c * B + M) ?_ _ hk
    intro t
    have h1 := exp_neg_le_one' a ha0 t
    rw [abs_of_nonneg (by have := hp.hc; have := ha0 t; positivity)]
    have := hp.hc
    nlinarith [hB t, exp_pos (-(a t))]
  have hcmp : ∀ a : Effort, Admissible a →
      (∫ t in Ioi 0, (p.c * x₀ + M * exp (-x₀)) * exp (-((v + p.r) * t))) ≤
      ∫ t in Ioi 0, (p.c * a t + M * exp (-(a t))) * exp (-((v + p.r) * t)) := by
    intro a ha
    refine setIntegral_mono_on (hint _ (admissible_const x₀ hx₀)) (hint a ha) measurableSet_Ioi ?_
    intro t _
    exact mul_le_mul_of_nonneg_right
      (pointwise_le p.c M x₀ hp.hc hM0 hx (a t) (ha.2.1 t)) (exp_pos _).le
  have hopt : AgentOptimal p (randomLaw v) P (fun _ => x₀) := by
    refine ⟨admissible_const x₀ hx₀, fun a' ha' => ?_⟩
    rw [agent_random p hp v hv P a' ha', agent_random p hp v hv P _ (admissible_const x₀ hx₀)]
    have := hcmp a' ha'
    nlinarith
  refine ⟨hopt, fun a ha => ?_⟩
  have hle := ha.2 _ (admissible_const x₀ hx₀)
  rw [agent_random p hp v hv P a ha.1, agent_random p hp v hv P _ (admissible_const x₀ hx₀)]
    at hle
  have hge := hcmp a ha.1
  have heq : (∫ t in Ioi 0, (p.c * a t + M * exp (-(a t))) * exp (-((v + p.r) * t))) -
      (∫ t in Ioi 0, (p.c * x₀ + M * exp (-x₀)) * exp (-((v + p.r) * t))) = 0 := by
    have : (∫ t in Ioi 0, (p.c * a t + M * exp (-(a t))) * exp (-((v + p.r) * t))) ≤
        ∫ t in Ioi 0, (p.c * x₀ + M * exp (-x₀)) * exp (-((v + p.r) * t)) := by
      by_contra h; push Not at h
      have := mul_lt_mul_of_pos_left h hkr
      linarith
    linarith
  rw [← integral_sub (hint a ha.1) (hint _ (admissible_const x₀ hx₀))] at heq
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun t =>
      (p.c * a t + M * exp (-(a t))) * exp (-((v + p.r) * t)) -
      (p.c * x₀ + M * exp (-x₀)) * exp (-((v + p.r) * t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [Pi.zero_apply]
    have := mul_le_mul_of_nonneg_right
      (pointwise_le p.c M x₀ hp.hc hM0 hx (a t) (ha.1.2.1 t)) (exp_pos (-((v + p.r) * t))).le
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn
    ((hint a ha.1).sub (hint _ (admissible_const x₀ hx₀)))).mp heq
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  filter_upwards [hz] with t ht
  simp only [Pi.zero_apply] at ht
  by_contra hne
  have := mul_lt_mul_of_pos_right
    (pointwise_strict p.c M x₀ hp.hc hM0 hx (a t) (ha.1.2.1 t) hne) (exp_pos (-((v + p.r) * t)))
  linarith
end RandomOpt

end OpInspCore

namespace OpInspCore
open OpRiskInspection.RandomVsPeriodic

section Periodic

lemma ii_bdd (a : Effort) (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) (B : ℝ) (hB : ∀ t, a t ≤ B)
    (x y : ℝ) : IntervalIntegrable a volume x y := by
  refine (intervalIntegrable_const (c := B)).mono_fun ha.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (ha0 s)]
  exact le_trans (hB s) (le_abs_self B)

lemma discF_periodic (p : Params) (v : ℝ) :
    discF p (periodicLaw v) = exp (-(p.r * (1 / v))) := by
  unfold discF periodicLaw; rw [integral_dirac]

lemma effortInt_periodic (p : Params) (v : ℝ) (a : Effort) :
    effortInt p (periodicLaw v) a = ∫ t in (0)..(1/v), a t * exp (-(p.r * t)) := by
  unfold effortInt periodicLaw; rw [integral_dirac]

lemma penaltyInt_periodic (p : Params) (v : ℝ) (a : Effort) :
    penaltyInt p (periodicLaw v) a =
      p.lam * exp (-(p.r * (1 / v))) * ∫ t in (0)..(1/v), exp (-(a t)) := by
  unfold penaltyInt periodicLaw expCount; rw [integral_dirac]; ring

lemma lossInt_periodic (p : Params) (v : ℝ) (a : Effort) :
    lossInt p (periodicLaw v) a = ∫ t in (0)..(1/v), expCount p a t * exp (-(p.r * t)) := by
  unfold lossInt periodicLaw; rw [integral_dirac]

/-- The periodic agent's objective integrand. -/
noncomputable def psiD (p : Params) (v P : ℝ) (a : Effort) (t : ℝ) : ℝ :=
  (p.c * a t + P * p.lam * exp (-(p.r * (1 / v - t))) * exp (-(a t))) * exp (-(p.r * t))

lemma psiD_ii (p : Params) (v P : ℝ) (a : Effort) (ha : Admissible a) (x y : ℝ) :
    IntervalIntegrable (psiD p v P a) volume x y := by
  obtain ⟨ham, ha0, B, hB⟩ := ha
  unfold psiD
  refine IntervalIntegrable.mul_continuousOn ?_ (by fun_prop)
  refine IntervalIntegrable.add ((ii_bdd a ham ha0 B hB x y).const_mul _) ?_
  have h1 := ii_expneg a ham ha0 x y
  have h2 : ContinuousOn (fun t => P * p.lam * exp (-(p.r * (1 / v - t)))) (uIcc x y) := by
    fun_prop
  have := h1.continuousOn_mul h2
  simpa [mul_comm, mul_assoc, mul_left_comm] using this

lemma agent_periodic (p : Params) (hp : Standing p) (v : ℝ) (hv : 0 < v) (P : ℝ)
    (a : Effort) (ha : Admissible a) :
    agentPayoff p (periodicLaw v) a P 0 =
      -(1 / (1 - exp (-(p.r * (1 / v))))) * ∫ t in (0)..(1/v), psiD p v P a t := by
  have ha' := ha
  obtain ⟨ham, ha0, B, hB⟩ := ha
  unfold agentPayoff
  rw [discF_periodic, effortInt_periodic, penaltyInt_periodic]
  have i1 : IntervalIntegrable (fun t => a t * exp (-(p.r * t))) volume 0 (1/v) :=
    (ii_bdd a ham ha0 B hB 0 (1/v)).mul_continuousOn (by fun_prop)
  have i2 := ii_expneg a ham ha0 0 (1/v)
  have e : ∫ t in (0)..(1/v), psiD p v P a t =
      p.c * (∫ t in (0)..(1/v), a t * exp (-(p.r * t))) +
      P * p.lam * exp (-(p.r * (1 / v))) * ∫ t in (0)..(1/v), exp (-(a t)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [psiD]
    have : exp (-(p.r * (1 / v - t))) * exp (-(p.r * t)) = exp (-(p.r * (1 / v))) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (P * p.lam * exp (-a t)) * this
  rw [e]
  ring

lemma periodic_opt (p : Params) (hp : Standing p) (v : ℝ) (hv : 0 < v) (P : ℝ) (hP : 0 ≤ P)
    (a₀ : Effort) (ha₀ : Admissible a₀)
    (hx : ∀ t ∈ Icc (0:ℝ) (1/v), (0 < a₀ t ∧
        (P * p.lam * exp (-(p.r * (1 / v - t)))) * exp (-(a₀ t)) = p.c) ∨
      (a₀ t = 0 ∧ P * p.lam * exp (-(p.r * (1 / v - t))) ≤ p.c)) :
    AgentOptimal p (periodicLaw v) P a₀ ∧
      ∀ a, AgentOptimal p (periodicLaw v) P a →
        ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (1/v))), a t = a₀ t := by
  have hr := hp.hr
  have hT : 0 ≤ 1 / v := by positivity
  have hD : 0 < 1 - exp (-(p.r * (1 / v))) := by
    have : exp (-(p.r * (1 / v))) < 1 := by
      have h0 : 0 < p.r * (1/v) := by positivity
      have := Real.exp_lt_exp.mpr (show -(p.r*(1/v)) < 0 by linarith)
      rwa [Real.exp_zero] at this
    linarith
  have hDinv : 0 < 1 / (1 - exp (-(p.r * (1 / v)))) := by positivity
  have hM0 : ∀ t : ℝ, 0 ≤ P * p.lam * exp (-(p.r * (1 / v - t))) := by
    intro t; have := hp.hlam; positivity
  have hpt : ∀ a : Effort, Admissible a → ∀ t ∈ Icc (0:ℝ) (1/v),
      psiD p v P a₀ t ≤ psiD p v P a t := by
    intro a ha t ht
    unfold psiD
    exact mul_le_mul_of_nonneg_right
      (pointwise_le p.c _ (a₀ t) hp.hc (hM0 t) (hx t ht) (a t) (ha.2.1 t)) (exp_pos _).le
  have hcmp : ∀ a : Effort, Admissible a →
      (∫ t in (0)..(1/v), psiD p v P a₀ t) ≤ ∫ t in (0)..(1/v), psiD p v P a t := by
    intro a ha
    exact intervalIntegral.integral_mono_on hT (psiD_ii p v P a₀ ha₀ _ _)
      (psiD_ii p v P a ha _ _) (hpt a ha)
  have hopt : AgentOptimal p (periodicLaw v) P a₀ := by
    refine ⟨ha₀, fun a' ha' => ?_⟩
    rw [agent_periodic p hp v hv P a' ha', agent_periodic p hp v hv P a₀ ha₀]
    have := mul_le_mul_of_nonneg_left (hcmp a' ha') hDinv.le
    linarith
  refine ⟨hopt, fun a ha => ?_⟩
  have hle := ha.2 a₀ ha₀
  rw [agent_periodic p hp v hv P a ha.1, agent_periodic p hp v hv P a₀ ha₀] at hle
  have hge := hcmp a ha.1
  have heq : (∫ t in (0)..(1/v), psiD p v P a t) - (∫ t in (0)..(1/v), psiD p v P a₀ t) = 0 := by
    have : (∫ t in (0)..(1/v), psiD p v P a t) ≤ ∫ t in (0)..(1/v), psiD p v P a₀ t := by
      by_contra h; push Not at h
      have := mul_lt_mul_of_pos_left h hDinv
      linarith
    linarith
  rw [← intervalIntegral.integral_sub (psiD_ii p v P a ha.1 _ _) (psiD_ii p v P a₀ ha₀ _ _),
    intervalIntegral.integral_of_le hT] at heq
  have hint : IntegrableOn (fun t => psiD p v P a t - psiD p v P a₀ t) (Ioc 0 (1/v)) :=
    ((psiD_ii p v P a ha.1 0 (1/v)).sub (psiD_ii p v P a₀ ha₀ 0 (1/v))).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) (1/v))] fun t =>
      psiD p v P a t - psiD p v P a₀ t := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    have := hpt a ha.1 t (Ioc_subset_Icc_self ht)
    simp only [Pi.zero_apply]; linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp heq
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioc] with t ht htm
  simp only [Pi.zero_apply] at ht
  by_contra hne
  have := mul_lt_mul_of_pos_right
    (pointwise_strict p.c _ (a₀ t) hp.hc (hM0 t) (hx t (Ioc_subset_Icc_self htm)) (a t)
      (ha.1.2.1 t) hne) (exp_pos (-(p.r * t)))
  simp only [psiD] at ht
  linarith

end Periodic
end OpInspCore

namespace OpInspCore
open OpRiskInspection.RandomVsPeriodic

lemma cond_of_y (c M y : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hy0 : 0 < y) (hMy : M * y = c) :
    (0 < -Real.log (min y 1) ∧ M * Real.exp (-(-Real.log (min y 1))) = c) ∨
      (-Real.log (min y 1) = 0 ∧ M ≤ c) := by
  rcases lt_or_ge y 1 with h | h
  · left
    rw [min_eq_left h.le, neg_neg, Real.exp_log hy0]
    exact ⟨by have := Real.log_neg hy0 h; linarith, hMy⟩
  · right
    rw [min_eq_right h, Real.log_one, neg_zero]
    exact ⟨rfl, by nlinarith⟩

/-- The periodic best response, clamped after the inspection date to keep it bounded. -/
noncomputable def aD (p : Params) (v P : ℝ) (t : ℝ) : ℝ :=
  -Real.log (min ((p.c / (P * p.lam)) * Real.exp (p.r * (1 / v - min t (1 / v)))) 1)

lemma aD_admissible (p : Params) (hp : Standing p) (v P : ℝ) (hv : 0 < v) (hP : 0 < P) :
    Admissible (aD p v P) := by
  have hk : 0 < p.c / (P * p.lam) := by have := hp.hc; have := hp.hlam; positivity
  refine ⟨?_, ?_, -Real.log (min (p.c / (P * p.lam)) 1), ?_⟩
  · unfold aD
    refine (Real.measurable_log.comp ?_).neg
    refine Measurable.min ?_ measurable_const
    refine measurable_const.mul (Measurable.exp ?_)
    exact measurable_const.mul (measurable_const.sub (measurable_id.min measurable_const))
  · intro t
    unfold aD
    have hpos : 0 < min ((p.c / (P * p.lam)) * Real.exp (p.r * (1 / v - min t (1 / v)))) 1 :=
      lt_min (by positivity) one_pos
    have := Real.log_nonpos hpos.le (min_le_right _ _); linarith
  · intro t
    unfold aD
    have h1 : 1 ≤ Real.exp (p.r * (1 / v - min t (1 / v))) := by
      apply Real.one_le_exp
      have := hp.hr
      have : min t (1/v) ≤ 1/v := min_le_right _ _
      nlinarith
    have hle : min (p.c / (P * p.lam)) 1 ≤
        min ((p.c / (P * p.lam)) * Real.exp (p.r * (1 / v - min t (1 / v)))) 1 :=
      min_le_min (by nlinarith) le_rfl
    have := Real.log_le_log (lt_min hk one_pos) hle
    linarith

lemma aD_eq (p : Params) (v P : ℝ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/v)) :
    aD p v P t = -Real.log (min ((p.c / (P * p.lam)) * Real.exp (p.r * (1 / v - t))) 1) := by
  unfold aD; rw [min_eq_left ht.2]

end OpInspCore


namespace OpInspCore
open OpRiskInspection.RandomVsPeriodic

lemma red_congr_periodic (p : Params) (K v : ℝ) (hv : 0 < v) (a a₀ : Effort)
    (hae : ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) (1/v))), a t = a₀ t) :
    reducedPayoff p K v (periodicLaw v) a = reducedPayoff p K v (periodicLaw v) a₀ := by
  have hT : 0 ≤ 1 / v := by positivity
  have h' : ∀ᵐ t, t ∈ Icc (0:ℝ) (1/v) → a t = a₀ t :=
    (ae_restrict_iff' measurableSet_Icc).mp hae
  have hE : effortInt p (periodicLaw v) a = effortInt p (periodicLaw v) a₀ := by
    rw [effortInt_periodic, effortInt_periodic]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [h'] with t ht hmem
    rw [Set.uIoc_of_le hT] at hmem
    rw [ht (Ioc_subset_Icc_self hmem)]
  have hC : ∀ t ∈ Icc (0:ℝ) (1/v), expCount p a t = expCount p a₀ t := by
    intro t htm
    unfold expCount
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [h'] with s hs hmem
    rw [Set.uIoc_of_le htm.1] at hmem
    rw [hs ⟨hmem.1.le, hmem.2.trans htm.2⟩]
  have hL : lossInt p (periodicLaw v) a = lossInt p (periodicLaw v) a₀ := by
    rw [lossInt_periodic, lossInt_periodic]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    simp only [hC t ht]
  unfold reducedPayoff
  rw [hE, hL]

lemma int_exp_lin (α β a b : ℝ) (hβ : β ≠ 0) :
    ∫ t in a..b, exp (α + β * t) = (exp (α + β * b) - exp (α + β * a)) / β := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => exp (α + β * t) / β)]
  · ring
  · intro t _
    have := (((hasDerivAt_id t).const_mul β).const_add α).exp.div_const β
    exact this.congr_deriv (by simp only [id]; field_simp)
  · exact (by fun_prop : Continuous fun t => exp (α + β * t)).intervalIntegrable _ _

lemma int_linexp (α r a b : ℝ) (hr : r ≠ 0) :
    ∫ t in a..b, (α + r * t) * exp (-(r * t)) =
      (-(α + r * b + 1) * exp (-(r * b)) + (α + r * a + 1) * exp (-(r * a))) / r := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -(α + r * t + 1) * exp (-(r * t)) / r)]
  · ring
  · intro t _
    have h1 : HasDerivAt (fun t => -(α + r * t + 1)) (-(r * 1)) t :=
      (((hasDerivAt_id t).const_mul r).const_add α |>.add_const 1).neg
    have h2 : HasDerivAt (fun t => exp (-(r * t))) (exp (-(r * t)) * (-(r * 1))) t :=
      ((hasDerivAt_id t).const_mul r).neg.exp
    have := (h1.mul h2).div_const r
    exact this.congr_deriv (by field_simp; ring)
  · exact (by fun_prop : Continuous fun t => (α + r * t) * exp (-(r * t))).intervalIntegrable _ _

lemma loss_swap (p : Params) (hr : 0 < p.r) (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ) :
    ∫ t in (0)..T, (p.lam * ∫ s in (0)..t, g s) * exp (-(p.r * t)) =
      p.lam / p.r * ∫ s in (0)..T, g s * (exp (-(p.r * s)) - exp (-(p.r * T))) := by
  have hu : ∀ x ∈ uIcc (0:ℝ) T, HasDerivAt (fun t => p.lam * ∫ s in (0)..t, g s)
      (p.lam * g x) x := fun x _ =>
    ((hg.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul p.lam
  have hW : ∀ x ∈ uIcc (0:ℝ) T, HasDerivAt
      (fun t => -(exp (-(p.r * t)) - exp (-(p.r * T))) / p.r) (exp (-(p.r * x))) x := by
    intro x _
    have := ((((hasDerivAt_id x).const_mul p.r).neg.exp).sub_const (exp (-(p.r * T)))).neg
      |>.div_const p.r
    exact this.congr_deriv (by simp only [id, Pi.neg_apply]; field_simp)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hW
    ((by fun_prop : Continuous fun x => p.lam * g x).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x => exp (-(p.r * x))).intervalIntegrable _ _)]
  have e0 : (p.lam * ∫ s in (0:ℝ)..0, g s) = 0 := by simp
  rw [e0]
  simp only [sub_self, neg_zero, zero_div, mul_zero, zero_mul, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  field_simp

lemma aD_cont (p : Params) (hp : Standing p) (v P : ℝ) (hP : 0 < P) :
    Continuous (aD p v P) := by
  have hk : 0 < p.c / (P * p.lam) := by have := hp.hc; have := hp.hlam; positivity
  unfold aD
  refine Continuous.neg (Continuous.log (by fun_prop) (fun t => ?_))
  exact (lt_min (by positivity) one_pos).ne'

/-- Values of the clamped best response on `[0, 1/v]`, with `m = log (Pλ/c)`. -/
lemma aD_val (p : Params) (hp : Standing p) (v P t : ℝ) (hP : p.c < P * p.lam)
    (ht : t ∈ Icc (0:ℝ) (1/v)) :
    (p.r * (1/v - t) ≤ Real.log (P * p.lam / p.c) →
      aD p v P t = Real.log (P * p.lam / p.c) - p.r * (1/v - t)) ∧
    (Real.log (P * p.lam / p.c) ≤ p.r * (1/v - t) → aD p v P t = 0) := by
  have hc := hp.hc
  have hM : 0 < P * p.lam / p.c := by
    have : 0 < P * p.lam := by linarith
    positivity
  have hk : p.c / (P * p.lam) * Real.exp (p.r * (1 / v - t)) =
      Real.exp (p.r * (1/v - t) - Real.log (P * p.lam / p.c)) := by
    rw [Real.exp_sub, Real.exp_log hM]
    have : P * p.lam ≠ 0 := by linarith
    field_simp
  rw [aD_eq p v P t ht, hk]
  constructor
  · intro h
    rw [min_eq_left (Real.exp_le_one_iff.mpr (by linarith)), Real.log_exp]; ring
  · intro h
    rw [min_eq_right (Real.one_le_exp (by linarith)), Real.log_one, neg_zero]

end OpInspCore

namespace OpInspCore
open OpRiskInspection.RandomVsPeriodic

lemma red_formula (p : Params) (hp : Standing p) (K v : ℝ) (hv : 0 < v) (a₀ : Effort)
    (hc : Continuous a₀) :
    reducedPayoff p K v (periodicLaw v) a₀ =
      mubar p / p.r - p.c * (∫ t in (0)..(1/v), a₀ t * exp (-(p.r * t))) /
        (1 - exp (-(p.r * (1 / v)))) -
      p.L * (p.lam / p.r * ∫ s in (0)..(1/v), exp (-(a₀ s)) *
        (exp (-(p.r * s)) - exp (-(p.r * (1/v))))) / (1 - exp (-(p.r * (1 / v)))) -
      K / (Real.exp (p.r / v) - 1) := by
  unfold reducedPayoff
  rw [discF_periodic, effortInt_periodic, lossInt_periodic]
  unfold expCount
  rw [loss_swap p hp.hr (fun s => exp (-(a₀ s))) (Real.continuous_exp.comp hc.neg) (1/v)]

lemma exp_mT (p : Params) (v : ℝ) : exp (-(p.r * (1 / v))) = 1 / Real.exp (p.r / v) := by
  rw [mul_one_div, Real.exp_neg]; ring

end OpInspCore

open OpRiskInspection.RandomVsPeriodic OpInspCore in
theorem solution (p : Params) (hp : Standing p)
    (K v P : ℝ) (hK : 0 < K) (hv : 0 < v) (hP : 0 ≤ P)
    (a : Effort) (ha : AgentOptimal p (periodicLaw v) P a) :
    (p.c / p.lam < P → vD p P < v →
      reducedPayoff p K v (periodicLaw v) a = VbarD p K v P) ∧
    (p.c / p.lam < P → v ≤ vD p P →
      reducedPayoff p K v (periodicLaw v) a = VunderD p K v P) ∧
    (P ≤ p.c / p.lam →
      reducedPayoff p K v (periodicLaw v) a = V0D p K v) := by
  have hr := hp.hr; have hc := hp.hc; have hlam := hp.hlam
  have hT : 0 < 1 / v := by positivity
  set E := Real.exp (p.r / v) with hEdef
  have hE1 : 1 < E := Real.one_lt_exp_iff.mpr (by positivity)
  have hET : exp (-(p.r * (1 / v))) = 1 / E := exp_mT p v
  have hx : p.r * (1 / v) = p.r / v := mul_one_div _ _
  have hI1 : ∫ s in (0:ℝ)..(1/v), (exp (-(p.r * s)) - exp (-(p.r * (1/v)))) =
      (1 - 1/E) / p.r - (1/v) / E := by
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun s => exp (-(p.r * s))).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, hET]
    have := int_exp_lin 0 (-p.r) 0 (1/v) (by linarith)
    simp only [zero_add, mul_zero, Real.exp_zero, neg_mul] at this
    rw [this, hET]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  -- Case P > c/λ: the effort is the clamped best response aD
  have hbig : p.c / p.lam < P →
      reducedPayoff p K v (periodicLaw v) a = reducedPayoff p K v (periodicLaw v) (aD p v P) := by
    intro hP'
    have hPl : p.c < P * p.lam := by rwa [div_lt_iff₀ hlam] at hP'
    have hP0 : 0 < P := by
      have := div_pos hc hlam; linarith
    have hopt := periodic_opt p hp v hv P hP0.le (aD p v P) (aD_admissible p hp v P hv hP0)
      (fun t ht => by
        rw [aD_eq p v P t ht]
        refine cond_of_y p.c _ _ hc (by positivity) (by positivity) ?_
        have : Real.exp (-(p.r * (1 / v - t))) * Real.exp (p.r * (1 / v - t)) = 1 := by
          rw [← Real.exp_add]; simp
        have h2 : P * p.lam * (p.c / (P * p.lam)) = p.c := by field_simp
        linear_combination (P * p.lam * (p.c / (P * p.lam))) * this + h2)
    exact red_congr_periodic p K v hv a _ (hopt.2 a ha)
  refine ⟨fun hP' hvD => ?_, fun hP' hvD => ?_, fun hP' => ?_⟩
  · -- regime (i)
    rw [hbig hP']
    have hPl : p.c < P * p.lam := by rwa [div_lt_iff₀ hlam] at hP'
    have hP0 : 0 < P := by
      have := div_pos hc hlam; linarith
    set M := P * p.lam / p.c with hMdef
    have hM : 1 < M := by rw [hMdef, one_lt_div hc]; exact hPl
    set m := Real.log M with hmdef
    have hm0 : 0 < m := Real.log_pos hM
    have hexpm : exp m = M := Real.exp_log (by linarith)
    have hxm : p.r / v < m := by
      rw [vD, div_lt_iff₀ hm0] at hvD
      rw [div_lt_iff₀ hv]; linarith
    have hval : ∀ t ∈ Icc (0:ℝ) (1/v), aD p v P t = (m - p.r * (1/v)) + p.r * t := by
      intro t ht
      rw [(aD_val p hp v P t hPl ht).1 (by rw [← hmdef]; nlinarith [ht.1])]
      ring
    rw [red_formula p hp K v hv _ (aD_cont p hp v P hP0)]
    have hEFF : ∫ t in (0:ℝ)..(1/v), aD p v P t * exp (-(p.r * t)) =
        (-(m + 1) / E + (m - p.r / v + 1)) / p.r := by
      rw [intervalIntegral.integral_congr (g := fun t => ((m - p.r * (1/v)) + p.r * t) *
        exp (-(p.r * t))) (fun t ht => by
          rw [Set.uIcc_of_le hT.le] at ht; simp only [hval t ht])]
      rw [int_linexp _ _ _ _ hr.ne', hET]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, add_zero]
      rw [hx]; ring
    have hLI : ∫ s in (0:ℝ)..(1/v), exp (-(aD p v P s)) *
        (exp (-(p.r * s)) - exp (-(p.r * (1/v)))) =
        (E / M - 1 / (E * M)) / (2 * p.r) - (1 / M - 1 / (E * M)) / p.r := by
      rw [intervalIntegral.integral_congr (g := fun s =>
          exp ((p.r * (1/v) - m) + (-2 * p.r) * s) - exp (-m + (-p.r) * s)) (fun t ht => by
          rw [Set.uIcc_of_le hT.le] at ht
          simp only [hval t ht]
          rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
          congr 1 <;> congr 1 <;> ring)]
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun s => exp ((p.r * (1/v) - m) + (-2 * p.r) * s)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s => exp (-m + (-p.r) * s)).intervalIntegrable _ _)]
      rw [int_exp_lin _ _ _ _ (by linarith), int_exp_lin _ _ _ _ (by linarith)]
      have e1 : exp ((p.r * (1/v) - m) + (-2 * p.r) * (1/v)) = 1 / (E * M) := by
        rw [show (p.r * (1/v) - m) + (-2 * p.r) * (1/v) = -(p.r * (1/v)) + -m by ring,
          Real.exp_add, hET, Real.exp_neg, hexpm]; field_simp
      have e2 : exp ((p.r * (1/v) - m) + (-2 * p.r) * 0) = E / M := by
        rw [show (p.r * (1/v) - m) + (-2 * p.r) * 0 = p.r / v - m by rw [hx]; ring,
          Real.exp_sub, hexpm]
      have e3 : exp (-m + (-p.r) * (1/v)) = 1 / (E * M) := by
        rw [show -m + (-p.r) * (1/v) = -(p.r * (1/v)) + -m by ring,
          Real.exp_add, hET, Real.exp_neg, hexpm]; field_simp
      have e4 : exp (-m + (-p.r) * 0) = 1 / M := by
        rw [show -m + (-p.r) * 0 = -m by ring, Real.exp_neg, hexpm]; ring
      rw [e1, e2, e3, e4]
      field_simp
      ring
    rw [hEFF, hLI, hET, VbarD]
    rw [← hmdef, ← hEdef]
    have hEM : E ≠ 1 := ne_of_gt hE1
    have hee : exp (-(p.r / v)) = 1 / E := by rw [Real.exp_neg]; ring
    rw [hee]
    have hPM : p.c / P = p.lam / M := by rw [hMdef]; field_simp
    have hE0 : E - 1 ≠ 0 := sub_ne_zero.mpr hEM
    have hE0' : 1 - 1 / E ≠ 0 := by
      rw [sub_ne_zero]; intro h; apply hEM; field_simp at h; linarith
    rw [show p.c * p.L / (P * p.r) = p.L * p.lam / (M * p.r) by
      rw [hMdef]; field_simp]
    field_simp
    ring
  · -- regime (ii)
    rw [hbig hP']
    have hPl : p.c < P * p.lam := by rwa [div_lt_iff₀ hlam] at hP'
    have hP0 : 0 < P := by
      have := div_pos hc hlam; linarith
    set M := P * p.lam / p.c with hMdef
    have hM : 1 < M := by rw [hMdef, one_lt_div hc]; exact hPl
    set m := Real.log M with hmdef
    have hm0 : 0 < m := Real.log_pos hM
    have hexpm : exp m = M := Real.exp_log (by linarith)
    have hmx : m ≤ p.r / v := by
      rw [vD, le_div_iff₀ hm0] at hvD
      rw [le_div_iff₀ hv]; linarith
    set t₁ := 1 / v - m / p.r with ht₁
    have ht₁0 : 0 ≤ t₁ := by
      rw [ht₁, sub_nonneg, div_le_div_iff₀ hr hv]
      rw [le_div_iff₀ hv] at hmx; linarith
    have ht₁T : t₁ ≤ 1 / v := by
      rw [ht₁]; have : 0 < m / p.r := by positivity
      linarith
    have hrt : p.r * t₁ = p.r / v - m := by rw [ht₁]; field_simp
    have hval1 : ∀ t ∈ Icc t₁ (1/v), aD p v P t = (m - p.r * (1/v)) + p.r * t := by
      intro t ht
      rw [(aD_val p hp v P t hPl ⟨ht₁0.trans ht.1, ht.2⟩).1 (by
        rw [← hmdef]; have := ht.1; nlinarith)]
      ring
    have hval0 : ∀ t ∈ Icc 0 t₁, aD p v P t = 0 := by
      intro t ht
      exact (aD_val p hp v P t hPl ⟨ht.1, ht.2.trans ht₁T⟩).2 (by
        rw [← hmdef]; have := ht.2; nlinarith)
    have hcont := aD_cont p hp v P hP0
    rw [red_formula p hp K v hv _ hcont]
    have he1 : exp (-(p.r * t₁)) = M / E := by
      rw [hrt, show -(p.r / v - m) = m - p.r / v by ring, Real.exp_sub, hexpm]
    have hEFF : ∫ t in (0:ℝ)..(1/v), aD p v P t * exp (-(p.r * t)) =
        (-(m + 1) / E + M / E) / p.r := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := t₁)
        ((by fun_prop : Continuous fun t => aD p v P t * exp (-(p.r * t))).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t => aD p v P t * exp (-(p.r * t))).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_congr (a := 0) (b := t₁) (g := fun _ => (0:ℝ)) (fun t ht => by
          rw [Set.uIcc_of_le ht₁0] at ht; simp only [hval0 t ht, zero_mul])]
      rw [intervalIntegral.integral_congr (a := t₁) (b := 1/v)
        (g := fun t => ((m - p.r * (1/v)) + p.r * t) *
        exp (-(p.r * t))) (fun t ht => by
          rw [Set.uIcc_of_le ht₁T] at ht; simp only [hval1 t ht])]
      rw [int_linexp _ _ _ _ hr.ne', hET, he1, intervalIntegral.integral_zero, hrt, hx]
      ring
    have hLI : ∫ s in (0:ℝ)..(1/v), exp (-(aD p v P s)) *
        (exp (-(p.r * s)) - exp (-(p.r * (1/v)))) =
        ((M / E - 1) / (-p.r) - t₁ / E) +
        ((1 / (E * M) - M / E) / (-2 * p.r) - (1 / (E * M) - 1 / E) / (-p.r)) := by
      have hcf : Continuous fun s => exp (-(aD p v P s)) *
          (exp (-(p.r * s)) - exp (-(p.r * (1/v)))) := by
        have := Real.continuous_exp.comp hcont.neg
        exact this.mul (by fun_prop)
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := t₁)
        (hcf.intervalIntegrable _ _) (hcf.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_congr (a := 0) (b := t₁) (g := fun s =>
          exp (0 + (-p.r) * s) - exp (-(p.r * (1/v)))) (fun t ht => by
          rw [Set.uIcc_of_le ht₁0] at ht
          simp only [hval0 t ht, neg_zero, Real.exp_zero, one_mul, zero_add, neg_mul])]
      rw [intervalIntegral.integral_congr (a := t₁) (b := 1/v) (g := fun s =>
          exp ((p.r * (1/v) - m) + (-2 * p.r) * s) - exp (-m + (-p.r) * s)) (fun t ht => by
          rw [Set.uIcc_of_le ht₁T] at ht
          simp only [hval1 t ht]
          rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
          congr 1 <;> congr 1 <;> ring)]
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun s => exp (0 + (-p.r) * s)).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun s => exp ((p.r * (1/v) - m) + (-2 * p.r) * s)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s => exp (-m + (-p.r) * s)).intervalIntegrable _ _)]
      rw [int_exp_lin _ _ _ _ (by linarith), int_exp_lin _ _ _ _ (by linarith),
        int_exp_lin _ _ _ _ (by linarith)]
      have e0 : exp (0 + (-p.r) * t₁) = M / E := by
        rw [show 0 + (-p.r) * t₁ = -(p.r * t₁) by ring, he1]
      have e0' : exp (0 + (-p.r) * 0) = 1 := by simp
      have e1 : exp ((p.r * (1/v) - m) + (-2 * p.r) * (1/v)) = 1 / (E * M) := by
        rw [show (p.r * (1/v) - m) + (-2 * p.r) * (1/v) = -(p.r * (1/v)) + -m by ring,
          Real.exp_add, hET, Real.exp_neg, hexpm]; field_simp
      have e2 : exp ((p.r * (1/v) - m) + (-2 * p.r) * t₁) = M / E := by
        rw [show (p.r * (1/v) - m) + (-2 * p.r) * t₁ = -(p.r * t₁) by linear_combination (-1:ℝ) * hrt + hx, he1]
      have e3 : exp (-m + (-p.r) * (1/v)) = 1 / (E * M) := by
        rw [show -m + (-p.r) * (1/v) = -(p.r * (1/v)) + -m by ring,
          Real.exp_add, hET, Real.exp_neg, hexpm]; field_simp
      have e4 : exp (-m + (-p.r) * t₁) = 1 / E := by
        rw [show -m + (-p.r) * t₁ = -(p.r / v) by rw [neg_mul, hrt]; ring, Real.exp_neg]; ring
      rw [e0, e0', e1, e2, e3, e4, hET, smul_eq_mul, sub_zero]
      ring
    rw [hEFF, hLI, hET, VunderD]
    have hvDm : p.r / vD p P = m := by rw [vD, ← hMdef, ← hmdef]; field_simp
    rw [hvDm, ← hmdef, ← hEdef, hexpm]
    have hEM : E ≠ 1 := ne_of_gt hE1
    have hE0 : E - 1 ≠ 0 := sub_ne_zero.mpr hEM
    have hE0' : 1 - 1 / E ≠ 0 := by
      rw [sub_ne_zero]; intro h; apply hEM; field_simp at h; linarith
    rw [show p.c * p.L / (P * p.r) = p.L * p.lam / (M * p.r) by
      rw [hMdef]; field_simp]
    rw [show P * p.lam / p.c = M from rfl, ht₁]
    field_simp
    ring
  · -- regime (iii): zero effort
    have hPl : P * p.lam ≤ p.c := by rwa [le_div_iff₀ hlam] at hP'
    have hopt := periodic_opt p hp v hv P hP (fun _ => 0) (admissible_const 0 le_rfl)
      (fun t ht => Or.inr ⟨rfl, by
        have h1 : Real.exp (-(p.r * (1 / v - t))) ≤ 1 := by
          rw [Real.exp_le_one_iff]; have := ht.2; nlinarith
        nlinarith [mul_nonneg hP hlam.le]⟩)
    rw [red_congr_periodic p K v hv a _ (hopt.2 a ha),
      red_formula p hp K v hv _ continuous_const]
    simp only [zero_mul, intervalIntegral.integral_zero, mul_zero, zero_div, sub_zero,
      neg_zero, Real.exp_zero, one_mul]
    rw [hI1, hET, V0D]
    have hEM : E ≠ 1 := ne_of_gt hE1
    have hE0 : E - 1 ≠ 0 := sub_ne_zero.mpr hEM
    have hE0' : 1 - 1 / E ≠ 0 := by
      rw [sub_ne_zero]; intro h; apply hEM; field_simp at h; linarith
    rw [← hEdef]
    field_simp
    ring
