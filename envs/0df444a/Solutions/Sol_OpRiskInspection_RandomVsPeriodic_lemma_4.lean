-- Prove2me | solution 1 for OpRiskInspection.RandomVsPeriodic.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:46:03.989539+00:00
-- url     : https://prove2.me/submissions/8cc5102a-f829-4b19-af42-f3f3f4b0f437

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

open OpRiskInspection.RandomVsPeriodic OpInspCore in
theorem solution (p : Params) (hp : Standing p) :
    (∀ (v P : ℝ), 0 < v → p.c / p.lam < P →
      ∃ a₀ : Effort,
        AgentOptimal p (periodicLaw v) P a₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (1 / v),
          Real.exp (-(a₀ t)) =
            min ((p.c / (P * p.lam)) *
              Real.exp (p.r * (1 / v - t))) 1) ∧
        (∀ a, AgentOptimal p (periodicLaw v) P a →
          ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (1 / v))),
            a t = a₀ t) ∧
        a₀ (0 : ℝ) < a₀ (1 / v) ∧
        (0 < a₀ 0 ↔ vD p P < v)) ∧
    (∀ (v P : ℝ), 0 < v → 0 ≤ P → P ≤ p.c / p.lam →
      AgentOptimal p (periodicLaw v) P (fun _ => 0) ∧
      ∀ a, AgentOptimal p (periodicLaw v) P a →
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (1 / v))),
          a t = 0) := by
  have hr := hp.hr; have hc := hp.hc; have hlam := hp.hlam
  constructor
  · intro v P hv hP
    have hPl : p.c < P * p.lam := by rwa [div_lt_iff₀ hlam] at hP
    have hP0 : 0 < P := by
      have := div_pos hc hlam; linarith
    have hk : 0 < p.c / (P * p.lam) := by positivity
    have hk1 : p.c / (P * p.lam) < 1 := by rw [div_lt_one (by positivity)]; exact hPl
    have hT : 0 ≤ 1 / v := by positivity
    refine ⟨aD p v P, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · intro t ht
      rw [aD_eq p v P t ht, neg_neg, Real.exp_log (lt_min (by positivity) one_pos)]
    rotate_left
    · rw [aD_eq p v P 0 ⟨le_rfl, hT⟩, aD_eq p v P (1/v) ⟨hT, le_rfl⟩, sub_self, mul_zero,
        Real.exp_zero, mul_one, min_eq_left hk1.le, sub_zero]
      have h1 : p.c / (P * p.lam) < min ((p.c / (P * p.lam)) * Real.exp (p.r * (1 / v))) 1 := by
        apply lt_min _ hk1
        have : 1 < Real.exp (p.r * (1 / v)) := Real.one_lt_exp_iff.mpr (by positivity)
        nlinarith
      have := Real.log_lt_log hk h1
      linarith
    · rw [aD_eq p v P 0 ⟨le_rfl, hT⟩, sub_zero]
      have hpos : 0 < (p.c / (P * p.lam)) * Real.exp (p.r * (1 / v)) := by positivity
      have hm : Real.log (P * p.lam / p.c) = -Real.log (p.c / (P * p.lam)) := by
        rw [← Real.log_inv, inv_div]
      have hm0 : 0 < Real.log (P * p.lam / p.c) := by
        rw [hm]; have := Real.log_neg hk hk1; linarith
      have key : (p.c / (P * p.lam)) * Real.exp (p.r * (1 / v)) < 1 ↔ vD p P < v := by
        rw [vD, div_lt_iff₀ hm0]
        rw [← Real.log_lt_log_iff hpos one_pos, Real.log_one, Real.log_mul hk.ne'
          (Real.exp_pos _).ne', Real.log_exp, hm]
        rw [show p.r * (1 / v) = p.r / v by ring]
        constructor
        · intro h
          have : p.r / v < Real.log (P * p.lam / p.c) := by rw [hm]; linarith
          rw [div_lt_iff₀ hv, hm] at this
          linarith [mul_comm (-Real.log (p.c / (P * p.lam))) v]
        · intro h
          have : p.r / v < -Real.log (p.c / (P * p.lam)) := by
            rw [div_lt_iff₀ hv]; linarith
          linarith
      rw [← key]
      constructor
      · intro h
        by_contra hn; push Not at hn
        rw [min_eq_right hn, Real.log_one, neg_zero] at h; exact lt_irrefl _ h
      · intro h
        rw [min_eq_left h.le]
        have := Real.log_neg hpos h; linarith
    all_goals
      have hopt := periodic_opt p hp v hv P hP0.le (aD p v P) (aD_admissible p hp v P hv hP0)
        (fun t ht => by
          rw [aD_eq p v P t ht]
          refine cond_of_y p.c _ _ hc (by positivity) (by positivity) ?_
          have : Real.exp (-(p.r * (1 / v - t))) * Real.exp (p.r * (1 / v - t)) = 1 := by
            rw [← Real.exp_add]; simp
          have h2 : P * p.lam * (p.c / (P * p.lam)) = p.c := by field_simp
          linear_combination (P * p.lam * (p.c / (P * p.lam))) * this + h2)
    · exact hopt.1
    · exact hopt.2
  · intro v P hv hP0 hP
    have hPl : P * p.lam ≤ p.c := by rwa [le_div_iff₀ hlam] at hP
    have := periodic_opt p hp v hv P hP0 (fun _ => 0) (admissible_const 0 le_rfl)
      (fun t ht => Or.inr ⟨rfl, by
        have h1 : Real.exp (-(p.r * (1 / v - t))) ≤ 1 := by
          rw [Real.exp_le_one_iff]; have := ht.2; nlinarith
        nlinarith [mul_nonneg hP0 hlam.le]⟩)
    exact this
