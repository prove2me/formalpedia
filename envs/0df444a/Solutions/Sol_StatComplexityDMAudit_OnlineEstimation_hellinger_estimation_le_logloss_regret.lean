-- Prove2me | solution 1 for StatComplexityDMAudit.OnlineEstimation.hellinger_estimation_le_logloss_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T18:24:45.637118+00:00
-- url     : https://prove2.me/submissions/fc87159b-6c15-43d6-8e09-19a90b4e13e2

import Mathlib
import Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Performance

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DCE06360Aux

open MeasureTheory ProbabilityTheory

/-- Pull-out: equal set integrals over `m`-sets give equal integrals against an
`m`-measurable weight. -/
theorem pullout {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) (μ : Measure[m0] Ω)
    {V Z A : Ω → ℝ≥0∞} (hV : Measurable[m] V) (hZ : Measurable[m0] Z) (hA : Measurable[m0] A)
    (h : ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, Z ω ∂μ = ∫⁻ ω in s, A ω ∂μ) :
    ∫⁻ ω, V ω * Z ω ∂μ = ∫⁻ ω, V ω * A ω ∂μ := by
  have e : (μ.withDensity Z).trim hm = (μ.withDensity A).trim hm := by
    refine @Measure.ext _ m _ _ (fun s hs => ?_)
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs,
      withDensity_apply _ (hm s hs), withDensity_apply _ (hm s hs)]
    exact h s hs
  have hV0 : Measurable[m0] V := hV.mono hm le_rfl
  calc ∫⁻ ω, V ω * Z ω ∂μ = ∫⁻ ω, V ω ∂(μ.withDensity Z) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hZ hV0]
        simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ ω, V ω ∂((μ.withDensity Z).trim hm) := (lintegral_trim hm hV).symm
    _ = ∫⁻ ω, V ω ∂((μ.withDensity A).trim hm) := by rw [e]
    _ = ∫⁻ ω, V ω ∂(μ.withDensity A) := lintegral_trim hm hV
    _ = ∫⁻ ω, V ω * A ω ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hA hV0]
        simp only [Pi.mul_apply, mul_comm]

theorem inv_mul_self_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  rcases eq_or_ne a ⊤ with h' | h'
  · simp [h']
  rw [ENNReal.inv_mul_cancel h h']

/-- The exponential supermartingale bound. -/
theorem prod_lintegral_le_one {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ℕ} (G : Fin T → MeasurableSpace Ω) (hG : ∀ t, G t ≤ m0)
    (Z A : Fin T → Ω → ℝ≥0∞) (hZ : ∀ t, Measurable (Z t))
    (hZG : ∀ s t : Fin T, s < t → Measurable[G t] (Z s))
    (hAG : ∀ s t : Fin T, s ≤ t → Measurable[G t] (A s))
    (hint : ∀ t s, MeasurableSet[G t] s → ∫⁻ ω in s, Z t ω ∂μ = ∫⁻ ω in s, A t ω ∂μ) :
    ∫⁻ ω, ∏ t, Z t ω * (A t ω)⁻¹ ∂μ ≤ 1 := by
  have key : ∀ k, k ≤ T →
      ∫⁻ ω, ∏ t ∈ Finset.univ.filter (fun t : Fin T => t.val < k), Z t ω * (A t ω)⁻¹ ∂μ ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      set tk : Fin T := ⟨k, by omega⟩ with htk
      have hset : Finset.univ.filter (fun t : Fin T => t.val < k + 1) =
          insert tk (Finset.univ.filter (fun t : Fin T => t.val < k)) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, htk,
          Fin.ext_iff]
        omega
      have hnot : tk ∉ Finset.univ.filter (fun t : Fin T => t.val < k) := by
        simp [htk]
      set P : Ω → ℝ≥0∞ := fun ω =>
        ∏ t ∈ Finset.univ.filter (fun t : Fin T => t.val < k), Z t ω * (A t ω)⁻¹ with hP
      have hPm : Measurable[G tk] P := by
        apply Finset.measurable_prod
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        have hlt : t < tk := by simp [Fin.lt_def, htk, ht]
        exact (hZG t tk hlt).mul (hAG t tk hlt.le).inv
      have hAm : Measurable (A tk) := (hAG tk tk le_rfl).mono (hG tk) le_rfl
      have hV : Measurable[G tk] (fun ω => P ω * (A tk ω)⁻¹) := hPm.mul (hAG tk tk le_rfl).inv
      calc ∫⁻ ω, ∏ t ∈ Finset.univ.filter (fun t : Fin T => t.val < k + 1),
              Z t ω * (A t ω)⁻¹ ∂μ
          = ∫⁻ ω, (P ω * (A tk ω)⁻¹) * Z tk ω ∂μ := by
            congr 1
            funext ω
            rw [hset, Finset.prod_insert hnot]
            simp only [hP]
            ring
        _ = ∫⁻ ω, (P ω * (A tk ω)⁻¹) * A tk ω ∂μ :=
            pullout (hG tk) μ hV (hZ tk) hAm (hint tk)
        _ ≤ ∫⁻ ω, P ω ∂μ := by
            apply lintegral_mono
            intro ω
            calc P ω * (A tk ω)⁻¹ * A tk ω = P ω * ((A tk ω)⁻¹ * A tk ω) := by ring
              _ ≤ P ω * 1 := by gcongr; exact inv_mul_self_le_one _
              _ = P ω := mul_one _
        _ ≤ 1 := ih (by omega)
  have := key T le_rfl
  simpa using this

/-- Pointwise identity: squared Hellinger integrand plus twice the affinity integrand. -/
theorem pt_identity (a b : ℝ≥0) :
    ENNReal.ofReal ((Real.sqrt (a : ℝ) - Real.sqrt (b : ℝ)) ^ 2) +
      2 * (StatComplexityDMAudit.OnlineEstimation.sqrtRatio b a * (b : ℝ≥0∞)) =
      (a : ℝ≥0∞) + (b : ℝ≥0∞) := by
  unfold StatComplexityDMAudit.OnlineEstimation.sqrtRatio
  have ha : (0 : ℝ) ≤ a := a.2
  have hb : (0 : ℝ) ≤ b := b.2
  split_ifs with h
  · subst h
    simp only [NNReal.coe_zero, Real.sqrt_zero, sub_zero, mul_zero, add_zero,
      ENNReal.coe_zero]
    rw [Real.sq_sqrt ha, ENNReal.ofReal_coe_nnreal]
  · have hbpos : (0 : ℝ) < b := lt_of_le_of_ne hb (by exact_mod_cast (Ne.symm h))
    have e1 : ENNReal.ofReal (Real.sqrt ((a : ℝ) / b)) * (b : ℝ≥0∞) =
        ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := b), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_div ha]
      field_simp
      rw [Real.sq_sqrt hb]
    rw [e1, ← ENNReal.ofReal_coe_nnreal (p := a), ← ENNReal.ofReal_coe_nnreal (p := b)]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (sq_nonneg _) (by positivity), ← ENNReal.ofReal_add ha hb]
    congr 1
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    nlinarith [h1, h2]

theorem measurable_sqrtRatio :
    Measurable (fun p : ℝ≥0 × ℝ≥0 => StatComplexityDMAudit.OnlineEstimation.sqrtRatio p.1 p.2) := by
  unfold StatComplexityDMAudit.OnlineEstimation.sqrtRatio
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const ?_
  fun_prop

open StatComplexityDMAudit.OnlineEstimation in
theorem logLoss_ne_bot (x : ℝ≥0) : logLoss x ≠ ⊥ := by
  unfold logLoss
  intro h
  rw [EReal.neg_eq_bot_iff, ENNReal.log_eq_top_iff] at h
  exact ENNReal.coe_ne_top h

open StatComplexityDMAudit.OnlineEstimation in
theorem logLoss_pos (x : ℝ≥0) (hx : x ≠ 0) : logLoss x = ((-Real.log (x : ℝ) : ℝ) : EReal) := by
  unfold logLoss
  have hxpos : (0 : ℝ) < x := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hx)
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.log_ofReal_of_pos hxpos, EReal.coe_neg]

open StatComplexityDMAudit.OnlineEstimation in
theorem logLoss_zero : logLoss 0 = ⊤ := by
  unfold logLoss
  simp

theorem sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_bot_iff.2 ⟨h a (Finset.mem_insert_self _ _),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))⟩

/-- The real coercion as an additive hom. -/
noncomputable def coeHom : ℝ →+ EReal where
  toFun := fun x => (x : EReal)
  map_zero' := rfl
  map_add' := fun x y => EReal.coe_add x y

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  map_sum coeHom f s

open StatComplexityDMAudit.OnlineEstimation in
theorem pointwise {T : ℕ} (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (Et At Zt : Fin T → ℝ≥0∞)
    (qv gv : Fin T → ℝ≥0) (hZ : ∀ t, Zt t = sqrtRatio (gv t) (qv t)) (hg : ∀ t, gv t ≠ 0)
    (hE : ∀ t, Et t + 2 * At t = 2) (hA : ∀ t, At t = 0 → Zt t = 0)
    (hW : ∏ t, Zt t * (At t)⁻¹ < ENNReal.ofReal δ⁻¹) (Linf : EReal)
    (hLinf : Linf ≤ ∑ t, logLoss (gv t)) :
    ((∑ t, Et t : ℝ≥0∞) : EReal) ≤
      (∑ t, logLoss (qv t)) - Linf + ((2 * Real.log (1 / δ) : ℝ) : EReal) := by
  have hgpos : ∀ t, (0 : ℝ) < (gv t : ℝ) := fun t =>
    lt_of_le_of_ne (gv t).coe_nonneg (fun h => hg t (by ext; simpa using h.symm))
  have hLg : ∑ t, logLoss (gv t) = ((∑ t, -Real.log (gv t : ℝ) : ℝ) : EReal) := by
    rw [coe_sum]; exact Finset.sum_congr rfl (fun t _ => logLoss_pos _ (hg t))
  by_cases hz : ∃ t, Zt t = 0
  · obtain ⟨t, ht⟩ := hz
    have hq : qv t = 0 := by
      rw [hZ t] at ht
      unfold sqrtRatio at ht
      rw [if_neg (hg t), ENNReal.ofReal_eq_zero] at ht
      have ht := le_antisymm ht (Real.sqrt_nonneg _)
      rw [Real.sqrt_eq_zero'] at ht
      have : (qv t : ℝ) ≤ 0 := by
        rcases (div_nonpos_iff.mp ht) with h | h
        · exact absurd h.2 (not_le.mpr (hgpos t))
        · exact h.1
      ext; exact le_antisymm this (qv t).coe_nonneg
    have htop : ∑ s, logLoss (qv s) = ⊤ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), hq, logLoss_zero]
      exact EReal.top_add_of_ne_bot (sum_ne_bot _ _ (fun i _ => logLoss_ne_bot _))
    have hLinf_ne : Linf ≠ ⊤ := by
      intro h
      rw [h, hLg] at hLinf
      exact EReal.coe_ne_top _ (top_le_iff.mp hLinf)
    rw [htop, EReal.top_sub hLinf_ne, EReal.top_add_coe]
    exact le_top
  push Not at hz
  -- all quantities are finite and positive
  have hA0 : ∀ t, At t ≠ 0 := fun t h => hz t (hA t h)
  have hA1 : ∀ t, At t ≤ 1 := by
    intro t
    have h2 : 2 * At t ≤ 2 := calc 2 * At t ≤ Et t + 2 * At t := le_add_self
      _ = 2 := hE t
    have : 2 * At t ≤ 2 * 1 := by simpa using h2
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 this
  have hAtop : ∀ t, At t ≠ ⊤ := fun t => ne_top_of_le_ne_top ENNReal.one_ne_top (hA1 t)
  set a : Fin T → ℝ := fun t => (At t).toReal with ha_def
  have hapos : ∀ t, 0 < a t := fun t => ENNReal.toReal_pos (hA0 t) (hAtop t)
  have hale : ∀ t, a t ≤ 1 := fun t => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hA1 t); simpa using this
  have hAa : ∀ t, At t = ENNReal.ofReal (a t) := fun t => (ENNReal.ofReal_toReal (hAtop t)).symm
  have hqpos : ∀ t, (0 : ℝ) < (qv t : ℝ) := by
    intro t
    refine lt_of_le_of_ne (qv t).coe_nonneg (fun h => hz t ?_)
    rw [hZ t]; unfold sqrtRatio; rw [if_neg (hg t), ← h]; simp
  set z : Fin T → ℝ := fun t => Real.sqrt ((qv t : ℝ) / (gv t : ℝ)) with hz_def
  have hzpos : ∀ t, 0 < z t := fun t => Real.sqrt_pos.2 (div_pos (hqpos t) (hgpos t))
  have hZz : ∀ t, Zt t = ENNReal.ofReal (z t) := fun t => by
    rw [hZ t]; unfold sqrtRatio; rw [if_neg (hg t)]
  have hlogz : ∀ t, Real.log (z t) = (Real.log (qv t : ℝ) - Real.log (gv t : ℝ)) / 2 := by
    intro t
    simp only [hz_def]
    rw [Real.log_sqrt (div_nonneg (qv t).coe_nonneg (gv t).coe_nonneg), Real.log_div (hqpos t).ne' (hgpos t).ne']
  -- product bound
  have hprod : ∏ t, Zt t * (At t)⁻¹ = ENNReal.ofReal (∏ t, z t / a t) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun t _ => div_nonneg (hzpos t).le (hapos t).le)]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [hZz t, hAa t, ← ENNReal.ofReal_inv_of_pos (hapos t), ← ENNReal.ofReal_mul (hzpos t).le,
      div_eq_mul_inv]
  rw [hprod, ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 hδ.1)] at hW
  have hPpos : 0 < ∏ t, z t / a t := Finset.prod_pos (fun t _ => div_pos (hzpos t) (hapos t))
  have hlog := Real.log_lt_log hPpos hW
  rw [Real.log_prod (fun t _ => (div_pos (hzpos t) (hapos t)).ne')] at hlog
  have hlog2 : ∑ t, (Real.log (z t) - Real.log (a t)) < Real.log (1 / δ) := by
    rw [one_div]
    refine lt_of_eq_of_lt (Finset.sum_congr rfl (fun t _ => ?_)) hlog
    rw [Real.log_div (hzpos t).ne' (hapos t).ne']
  -- the Hellinger sum
  have hEt : ∀ t, Et t = ENNReal.ofReal (2 - 2 * a t) := by
    intro t
    have h1 : Et t = 2 - 2 * At t :=
      ENNReal.eq_sub_of_add_eq (ENNReal.mul_ne_top (by norm_num) (hAtop t)) (hE t)
    rw [h1, hAa t, ENNReal.ofReal_sub _ (by nlinarith [hapos t]), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hEsum : (∑ t, Et t : ℝ≥0∞) = ENNReal.ofReal (∑ t, (2 - 2 * a t)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by nlinarith [hale t])]
    exact Finset.sum_congr rfl (fun t _ => hEt t)
  have hLq : ∑ t, logLoss (qv t) = ((∑ t, -Real.log (qv t : ℝ) : ℝ) : EReal) := by
    rw [coe_sum]
    exact Finset.sum_congr rfl (fun t _ => logLoss_pos _ (fun h => (hqpos t).ne' (by simp [h])))
  have hreal : ∑ t, (2 - 2 * a t) ≤
      (∑ t, -Real.log (qv t : ℝ)) - (∑ t, -Real.log (gv t : ℝ)) + 2 * Real.log (1 / δ) := by
    have hterm : ∀ t, 2 - 2 * a t ≤
        2 * (Real.log (z t) - Real.log (a t)) + (-Real.log (qv t : ℝ) - -Real.log (gv t : ℝ)) := by
      intro t
      have h1 := Real.log_le_sub_one_of_pos (hapos t)
      rw [hlogz t]
      linarith
    calc ∑ t, (2 - 2 * a t)
        ≤ ∑ t, (2 * (Real.log (z t) - Real.log (a t)) +
            (-Real.log (qv t : ℝ) - -Real.log (gv t : ℝ))) := Finset.sum_le_sum (fun t _ => hterm t)
      _ = 2 * ∑ t, (Real.log (z t) - Real.log (a t)) +
            ((∑ t, -Real.log (qv t : ℝ)) - (∑ t, -Real.log (gv t : ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ _ := by linarith
  rw [hEsum, EReal.coe_ennreal_ofReal, hLq]
  have hnn : max (∑ t, (2 - 2 * a t)) 0 = ∑ t, (2 - 2 * a t) :=
    max_eq_left (Finset.sum_nonneg (fun t _ => by nlinarith [hale t]))
  rw [hnn]
  calc ((∑ t, (2 - 2 * a t) : ℝ) : EReal)
      ≤ (((∑ t, -Real.log (qv t : ℝ)) - (∑ t, -Real.log (gv t : ℝ)) +
          2 * Real.log (1 / δ) : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hreal
    _ = ((∑ t, -Real.log (qv t : ℝ) : ℝ) : EReal) - ((∑ t, -Real.log (gv t : ℝ) : ℝ) : EReal) +
          ((2 * Real.log (1 / δ) : ℝ) : EReal) := by
        rw [EReal.coe_add, EReal.coe_sub]
    _ ≤ _ := by
        gcongr
        exact EReal.sub_le_sub le_rfl (hLg ▸ hLinf)

section Concrete

open StatComplexityDMAudit.OnlineEstimation

variable {Ω I X Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {T : ℕ}

theorem history_meas (o : Observations Ω X Y T) (t : Fin T) : Measurable (o.history t) :=
  measurable_pi_lambda _ (fun _ => o.measurable_obs _)

theorem past_le (o : Observations Ω X Y T) (t : Fin T) : o.past t ≤ mΩ :=
  (history_meas o t).comap_le

theorem current_meas (o : Observations Ω X Y T) (t : Fin T) :
    Measurable (fun ω => (o.history t ω, (o.obs t ω).1)) :=
  (history_meas o t).prodMk (o.measurable_obs t).fst

theorem current_le (o : Observations Ω X Y T) (t : Fin T) : o.current t ≤ mΩ :=
  (current_meas o t).comap_le

theorem past_le_current (o : Observations Ω X Y T) (t : Fin T) : o.past t ≤ o.current t := by
  have : Measurable[o.current t] (o.history t) :=
    measurable_fst.comp (comap_measurable (fun ω => (o.history t ω, (o.obs t ω).1)))
  exact this.comap_le

theorem hist_meas_past (o : Observations Ω X Y T) {s t : Fin T} (h : s ≤ t) :
    Measurable[o.past t] (o.history s) := by
  have hh : Measurable[o.past t] (o.history t) := comap_measurable _
  have e : o.history s =
      fun ω => fun j : Fin s.val => o.history t ω ⟨j.val, lt_of_lt_of_le j.2 h⟩ := rfl
  have hR : Measurable (fun (f : History X Y t.val) (j : Fin s.val) =>
      f ⟨j.val, lt_of_lt_of_le j.2 h⟩) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  rw [e]
  exact hR.comp hh

theorem past_mono (o : Observations Ω X Y T) {s t : Fin T} (h : s ≤ t) :
    o.past s ≤ o.past t := (hist_meas_past o h).comap_le

theorem obs_meas_past (o : Observations Ω X Y T) {s t : Fin T} (h : s < t) :
    Measurable[o.past t] (o.obs s) := by
  have hh : Measurable[o.past t] (o.history t) := comap_measurable _
  have e : o.obs s = fun ω => o.history t ω ⟨s.val, h⟩ := rfl
  rw [e]
  exact (measurable_pi_apply _).comp hh

/-- Square-root likelihood ratio of the learner to the true expert at the realized outcome. -/
noncomputable def Zf (o : Observations Ω X Y T) {ν : Kernel X Y} (q gs : Predictor ν T)
    (t : Fin T) (ω : Ω) : ℝ≥0∞ :=
  sqrtRatio (densityAt o gs t ω (o.obs t ω).2) (densityAt o q t ω (o.obs t ω).2)

theorem Zf_eq (o : Observations Ω X Y T) {ν : Kernel X Y} (q gs : Predictor ν T) (t : Fin T) :
    Zf o q gs t = (fun p : History X Y t.val × (X × Y) => sqrtRatio ((gs t).value p) ((q t).value p))
      ∘ (fun ω => (o.history t ω, o.obs t ω)) := rfl

omit mΩ in
theorem F_meas {ν : Kernel X Y} (q gs : Predictor ν T) (t : Fin T) :
    Measurable (fun p : History X Y t.val × (X × Y) =>
      sqrtRatio ((gs t).value p) ((q t).value p)) :=
  measurable_sqrtRatio.comp ((gs t).measurable_value.prodMk (q t).measurable_value)

theorem Zf_meas (o : Observations Ω X Y T) {ν : Kernel X Y} (q gs : Predictor ν T) (t : Fin T) :
    Measurable (Zf o q gs t) := by
  rw [Zf_eq]
  exact (F_meas q gs t).comp ((history_meas o t).prodMk (o.measurable_obs t))

theorem Zf_meas_past (o : Observations Ω X Y T) {ν : Kernel X Y} (q gs : Predictor ν T)
    {s t : Fin T} (h : s < t) : Measurable[o.past t] (Zf o q gs s) := by
  rw [Zf_eq]
  exact (F_meas q gs s).comp ((hist_meas_past o h.le).prodMk (obs_meas_past o h))

/-- The realizability test function for `Zf`. -/
noncomputable def fZ {ν : Kernel X Y} (q gs : Predictor ν T) (t : Fin T) :
    (History X Y t.val × X) × Y → ℝ≥0∞ :=
  fun p => sqrtRatio ((gs t).value (p.1.1, (p.1.2, p.2))) ((q t).value (p.1.1, (p.1.2, p.2)))

theorem fZ_meas {ν : Kernel X Y} (q gs : Predictor ν T) (t : Fin T) :
    Measurable (fZ q gs t) := by
  have hp : Measurable (fun p : (History X Y t.val × X) × Y => (p.1.1, (p.1.2, p.2))) := by
    fun_prop
  exact measurable_sqrtRatio.comp
    (((gs t).measurable_value.comp hp).prodMk ((q t).measurable_value.comp hp))

/-- The conditional affinity (true expert against the learner) at round `t`. -/
noncomputable def aff (o : Observations Ω X Y T) {ν : Kernel X Y} (q gs : Predictor ν T)
    (t : Fin T) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ y, fZ q gs t ((o.history t ω, (o.obs t ω).1), y) * (densityAt o gs t ω y : ℝ≥0∞)
    ∂ν ((o.obs t ω).1)

theorem round_identity (o : Observations Ω X Y T) {ν : Kernel X Y} (q : Predictor ν T)
    (g : I → Predictor ν T) (istar : I) (t : Fin T) (ω : Ω) :
    roundHellinger o q g istar t ω + 2 * aff o q (g istar) t ω = 2 := by
  have hq : Measurable (densityAt o q t ω) :=
    (q t).measurable_value.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hg : Measurable (densityAt o (g istar) t ω) :=
    (g istar t).measurable_value.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h1 : Measurable (fun y => ENNReal.ofReal
      ((Real.sqrt (densityAt o q t ω y : ℝ) - Real.sqrt (densityAt o (g istar) t ω y : ℝ)) ^ 2)) := by
    fun_prop
  have h2 : Measurable (fun y => fZ q (g istar) t ((o.history t ω, (o.obs t ω).1), y) *
      (densityAt o (g istar) t ω y : ℝ≥0∞)) :=
    ((fZ_meas q (g istar) t).comp (measurable_const.prodMk measurable_id)).mul
      (measurable_coe_nnreal_ennreal.comp hg)
  have nq : ∫⁻ y, (densityAt o q t ω y : ℝ≥0∞) ∂ν ((o.obs t ω).1) = 1 := (q t).normalized _ _
  have ng : ∫⁻ y, (densityAt o (g istar) t ω y : ℝ≥0∞) ∂ν ((o.obs t ω).1) = 1 :=
    (g istar t).normalized _ _
  unfold roundHellinger hellingerSq aff
  rw [← lintegral_const_mul 2 h2, ← lintegral_add_left h1]
  calc _ = ∫⁻ y, ((densityAt o q t ω y : ℝ≥0∞) + densityAt o (g istar) t ω y)
        ∂ν ((o.obs t ω).1) := lintegral_congr (fun y => pt_identity _ _)
    _ = 2 := by
      rw [lintegral_add_left hq.coe_nnreal_ennreal, nq, ng]
      exact one_add_one_eq_two

end Concrete

section Rounds

open StatComplexityDMAudit.OnlineEstimation

variable {Ω I X Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {T : ℕ}

theorem round_E {ν : Kernel X Y} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (o : Observations Ω X Y T) (q : Predictor ν T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar) (t : Fin T) :
    ∀ᵐ ω ∂μ, condLExp (o.past t) μ (roundHellinger o q g istar t) ω +
      2 * condLExp (o.past t) μ (Zf o q (g istar) t) ω = 2 := by
  have hm := past_le o t
  have hpc := past_le_current o t
  have hr : condLExp (o.current t) μ (Zf o q (g istar) t) =ᵐ[μ] aff o q (g istar) t :=
    hreal t _ (fZ_meas q (g istar) t)
  have haffm : AEMeasurable (aff o q (g istar) t) μ :=
    ((measurable_condLExp' (o.current t) μ _).aemeasurable).congr hr
  have hY : Measurable[o.past t] (fun ω => condLExp (o.past t) μ (roundHellinger o q g istar t) ω +
      2 * condLExp (o.past t) μ (Zf o q (g istar) t) ω) :=
    (measurable_condLExp _ _ _).add (measurable_const.mul (measurable_condLExp _ _ _))
  have key := ae_eq_condLExp hm μ (fun _ => (2 : ℝ≥0∞)) hY ?_
  · rw [condLExp_const hm] at key
    exact key
  intro s hs
  rw [lintegral_add_left (measurable_condLExp' _ _ _),
    lintegral_const_mul _ (measurable_condLExp' _ _ _), setLIntegral_condLExp hm _ _ hs,
    setLIntegral_condLExp hm _ _ hs,
    ← setLIntegral_condLExp (current_le o t) μ (Zf o q (g istar) t) (hpc s hs),
    lintegral_congr_ae (ae_restrict_of_ae hr),
    ← lintegral_const_mul'' _ haffm.restrict,
    ← lintegral_add_right' _ (haffm.restrict.const_mul 2)]
  exact lintegral_congr (fun ω => round_identity o q g istar t ω)

theorem round_A0 {ν : Kernel X Y} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (o : Observations Ω X Y T) (q : Predictor ν T) (gs : Predictor ν T) (t : Fin T) :
    ∀ᵐ ω ∂μ, condLExp (o.past t) μ (Zf o q gs t) ω = 0 → Zf o q gs t ω = 0 := by
  have hm := past_le o t
  have hs : MeasurableSet[o.past t] {ω | condLExp (o.past t) μ (Zf o q gs t) ω = 0} :=
    measurable_condLExp _ _ _ (measurableSet_singleton 0)
  have hZm : Measurable (Zf o q gs t) := Zf_meas o q gs t
  have h0 : ∫⁻ ω in {ω | condLExp (o.past t) μ (Zf o q gs t) ω = 0}, Zf o q gs t ω ∂μ = 0 := by
    rw [← setLIntegral_condLExp hm μ _ hs]
    have : ∀ᵐ ω ∂(μ.restrict {ω | condLExp (o.past t) μ (Zf o q gs t) ω = 0}),
        condLExp (o.past t) μ (Zf o q gs t) ω = 0 :=
      (ae_restrict_iff' (hm _ hs)).2 (Filter.Eventually.of_forall fun ω hω => hω)
    rw [lintegral_congr_ae this, lintegral_zero]
  have h1 := (ae_restrict_iff' (hm _ hs)).1 ((lintegral_eq_zero_iff hZm).1 h0)
  filter_upwards [h1] with ω h hA
  simpa using h hA

theorem round_gpos {ν : Kernel X Y} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (o : Observations Ω X Y T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar) (t : Fin T) :
    ∀ᵐ ω ∂μ, densityAt o (g istar) t ω (o.obs t ω).2 ≠ 0 := by
  have hp : Measurable (fun p : (History X Y t.val × X) × Y => (p.1.1, (p.1.2, p.2))) := by
    fun_prop
  set fN : (History X Y t.val × X) × Y → ℝ≥0∞ :=
    fun p => if (g istar t).value (p.1.1, (p.1.2, p.2)) = 0 then 1 else 0 with hfN_def
  have hfN : Measurable fN :=
    Measurable.ite (measurableSet_eq_fun ((g istar t).measurable_value.comp hp) measurable_const)
      measurable_const measurable_const
  have hr := hreal t fN hfN
  have hNm : Measurable (fun ω => fN ((o.history t ω, (o.obs t ω).1), (o.obs t ω).2)) :=
    hfN.comp ((current_meas o t).prodMk (o.measurable_obs t).snd)
  have hzero : ∀ ω, ∫⁻ y, fN ((o.history t ω, (o.obs t ω).1), y) *
      (densityAt o (g istar) t ω y : ℝ≥0∞) ∂ν ((o.obs t ω).1) = 0 := by
    intro ω
    rw [← lintegral_zero]
    refine lintegral_congr (fun y => ?_)
    simp only [hfN_def]
    split_ifs with h
    · simp [densityAt, h]
    · simp
  have hint : ∫⁻ ω, fN ((o.history t ω, (o.obs t ω).1), (o.obs t ω).2) ∂μ = 0 := by
    rw [← lintegral_condLExp (current_le o t) μ, lintegral_congr_ae hr]
    simp [hzero]
  have h1 := (lintegral_eq_zero_iff hNm).1 hint
  filter_upwards [h1] with ω hω h0
  have : fN ((o.history t ω, (o.obs t ω).1), (o.obs t ω).2) = 1 := by
    simp only [hfN_def]
    exact if_pos h0
  rw [this] at hω
  simp at hω

end Rounds

open StatComplexityDMAudit.OnlineEstimation in
theorem main_aux {Ω I X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {T : ℕ} (ν : Kernel X Y) (μ : Measure Ω) [IsProbabilityMeasure μ] (o : Observations Ω X Y T)
    (q : Predictor ν T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ μ E ∧
      ∀ ω ∈ E, (estH μ o q g istar ω : EReal) ≤
        regKL o q g ω + (2 * Real.log (1 / δ) : ℝ) := by
  set Z : Fin T → Ω → ℝ≥0∞ := fun t => Zf o q (g istar) t with hZdef
  set A : Fin T → Ω → ℝ≥0∞ := fun t => condLExp (o.past t) μ (Z t) with hAdef
  set W : Ω → ℝ≥0∞ := fun ω => ∏ t, Z t ω * (A t ω)⁻¹ with hWdef
  have hZm : ∀ t, Measurable (Z t) := fun t =>
    Zf_meas o q _ t
  have hWm : Measurable W :=
    Finset.measurable_prod _ (fun t _ => (hZm t).mul (measurable_condLExp' _ _ _).inv)
  have hWint : ∫⁻ ω, W ω ∂μ ≤ 1 :=
    prod_lintegral_le_one μ (fun t => o.past t) (fun t => past_le o t) Z A hZm
      (fun s t hst => Zf_meas_past o q _ hst)
      (fun s t hst => (measurable_condLExp (o.past s) μ (Z s)).mono (past_mono o hst) le_rfl)
      (fun t s hs => (setLIntegral_condLExp (past_le o t) μ (Z t) hs).symm)
  set B : Set Ω := {ω | ENNReal.ofReal δ⁻¹ ≤ W ω} with hBdef
  have hBm : MeasurableSet B := measurableSet_le measurable_const hWm
  have hB : μ B ≤ ENNReal.ofReal δ := by
    have h1 := mul_meas_ge_le_lintegral₀ (μ := μ) hWm.aemeasurable (ENNReal.ofReal δ⁻¹)
    have h2 : ENNReal.ofReal δ⁻¹ * μ B ≤ 1 := h1.trans hWint
    have hpos : ENNReal.ofReal δ⁻¹ ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hδ.1
    have htop : ENNReal.ofReal δ⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc μ B = (ENNReal.ofReal δ⁻¹)⁻¹ * (ENNReal.ofReal δ⁻¹ * μ B) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
      _ ≤ (ENNReal.ofReal δ⁻¹)⁻¹ * 1 := by gcongr
      _ = ENNReal.ofReal δ := by
          rw [mul_one, ← ENNReal.ofReal_inv_of_pos (inv_pos.2 hδ.1), inv_inv]
  have hgood : ∀ᵐ ω ∂μ, ∀ t, (condLExp (o.past t) μ (roundHellinger o q g istar t) ω +
      2 * A t ω = 2) ∧ (A t ω = 0 → Z t ω = 0) ∧
      densityAt o (g istar) t ω (o.obs t ω).2 ≠ 0 := by
    rw [ae_all_iff]
    intro t
    filter_upwards [round_E μ o q g istar hreal t, round_A0 μ o q (g istar) t,
      round_gpos μ o g istar hreal t] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨N, hNsup, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  refine ⟨Bᶜ ∩ Nᶜ, hBm.compl.inter hNm.compl, ?_, ?_⟩
  · have h1 : μ Bᶜ ≤ μ (Bᶜ ∩ Nᶜ) + μ N := by
      calc μ Bᶜ ≤ μ ((Bᶜ ∩ Nᶜ) ∪ N) := by
            apply measure_mono
            intro ω hω
            by_cases h : ω ∈ N
            · exact Or.inr h
            · exact Or.inl ⟨hω, h⟩
        _ ≤ _ := measure_union_le _ _
    rw [hN0, add_zero, prob_compl_eq_one_sub hBm] at h1
    refine le_trans ?_ h1
    rw [ENNReal.ofReal_sub _ hδ.1.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hB 1
  · intro ω hω
    have hωB : ω ∉ B := hω.1
    have hωg : ∀ t, (condLExp (o.past t) μ (roundHellinger o q g istar t) ω +
        2 * A t ω = 2) ∧ (A t ω = 0 → Z t ω = 0) ∧
        densityAt o (g istar) t ω (o.obs t ω).2 ≠ 0 := by
      by_contra hc
      exact hω.2 (hNsup hc)
    have hW : W ω < ENNReal.ofReal δ⁻¹ := not_le.1 hωB
    unfold estH regKL cumulativeLoss
    exact pointwise δ hδ (fun t => condLExp (o.past t) μ (roundHellinger o q g istar t) ω)
      (fun t => A t ω) (fun t => Z t ω) (fun t => densityAt o q t ω (o.obs t ω).2)
      (fun t => densityAt o (g istar) t ω (o.obs t ω).2) (fun t => rfl)
      (fun t => (hωg t).2.2) (fun t => (hωg t).1) (fun t => (hωg t).2.1) hW _
      (iInf_le _ istar)

end DCE06360Aux

open StatComplexityDMAudit.OnlineEstimation MeasureTheory ProbabilityTheory in
theorem solution {Ω I X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ}
    (ν : Kernel X Y) (hν : ∀ x, SigmaFinite (ν x))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : Observations Ω X Y T)
    (q : Predictor ν T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ μ E ∧
      ∀ ω ∈ E, (estH μ o q g istar ω : EReal) ≤
        regKL o q g ω + (2 * Real.log (1 / δ) : ℝ) := by
  clear hν
  exact DCE06360Aux.main_aux ν μ o q g istar hreal δ hδ
