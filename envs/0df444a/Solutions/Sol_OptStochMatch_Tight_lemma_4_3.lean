-- Prove2me | solution 1 for OptStochMatch.Tight.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:55.035904+00:00
-- url     : https://prove2.me/submissions/0120c4a1-6519-4365-80a8-9d3033aa0b7c

import Definitions.Def_OptStochMatch_Tight_Comparison

namespace AuxLemma43

open MeasureTheory ProbabilityTheory Set OptStochMatch.Tight

lemma compTraj_eq (t h : ℝ) :
    compTraj t h = fun v => (h + 1) * Real.exp (v - t) - 1 := by
  let ψ₀ : ℝ → ℝ := fun v => (h + 1) * Real.exp (v - t) - 1
  have hψ₀ : ψ₀ t = h ∧ ∀ v, HasDerivAt ψ₀ (ψ₀ v + 1) v := by
    refine ⟨by simp [ψ₀], fun v => ?_⟩
    have h1 : HasDerivAt (fun u => u - t) 1 v := (hasDerivAt_id v).sub_const t
    have h2 : HasDerivAt (fun u => Real.exp (u - t)) (Real.exp (v - t)) v := by
      simpa using h1.exp
    have h3 : HasDerivAt ψ₀ ((h + 1) * Real.exp (v - t)) v := by
      simpa [ψ₀] using (h2.const_mul (h + 1)).sub_const 1
    convert h3 using 1
    simp [ψ₀]
  have hspec : compTraj t h t = h ∧ ∀ v, HasDerivAt (compTraj t h) (compTraj t h v + 1) v :=
    Classical.epsilon_spec (p := fun ψ : ℝ → ℝ => ψ t = h ∧ ∀ v, HasDerivAt ψ (ψ v + 1) v)
      ⟨ψ₀, hψ₀⟩
  funext v
  let g : ℝ → ℝ := fun u => (compTraj t h u + 1) * Real.exp (t - u)
  have hg_deriv : ∀ u, HasDerivAt g 0 u := by
    intro u
    have ha : HasDerivAt (fun w => compTraj t h w + 1) (compTraj t h u + 1) u :=
      (hspec.2 u).add_const 1
    have hb : HasDerivAt (fun w => Real.exp (t - w)) (-Real.exp (t - u)) u := by
      have hsub : HasDerivAt (fun w => t - w) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub t
      have hexp := hsub.exp
      have hrew : Real.exp (t - u) * -1 = -Real.exp (t - u) := by ring
      exact hrew ▸ hexp
    have hm := ha.mul hb
    have hzero : (compTraj t h u + 1) * Real.exp (t - u) +
        (compTraj t h u + 1) * -Real.exp (t - u) = 0 := by ring
    exact hzero ▸ hm
  have hg_const : g v = g t :=
    is_const_of_deriv_eq_zero (fun u => (hg_deriv u).differentiableAt)
      (fun u => (hg_deriv u).deriv) v t
  have hgt : g t = h + 1 := by simp [g, hspec.1]
  have hmul : compTraj t h v + 1 = g v * Real.exp (v - t) := by
    dsimp [g]
    rw [mul_assoc, ← Real.exp_add]
    simp
  rw [hg_const, hgt] at hmul
  linarith

lemma expOne_real_Iic (x : ℝ) :
    expOne.real (Iic x) = if 0 ≤ x then 1 - Real.exp (-x) else 0 := by
  rw [← cdf_eq_real]
  change (cdf (expMeasure 1)) x = _
  simpa using cdf_expMeasure_eq (r := 1) (by norm_num) x

lemma expOne_ae_pos : ∀ᵐ e ∂expOne, 0 < e := by
  rw [ae_iff]
  have hset : {e : ℝ | ¬ 0 < e} = Iic 0 := by ext e; simp
  rw [hset]
  apply (measureReal_eq_zero_iff (s := Iic 0)).mp
  simp [expOne_real_Iic]

instance expOne_nullSingleton : NullSingletonClass expOne :=
  ⟨fun x => by simp [expOne, expMeasure, gammaMeasure]⟩

noncomputable def capExp (B : ℝ) : ℝ :=
  if B < 0 then B else 1 - Real.exp (-B)

lemma integral_min_expOne (B : ℝ) :
    (∫ e, min e B ∂expOne) = capExp B := by
  by_cases hB : B < 0
  · rw [capExp, if_pos hB]
    have hae : (fun e : ℝ => min e B) =ᵐ[expOne] fun _ => B := by
      filter_upwards [expOne_ae_pos] with e he
      exact min_eq_right (le_of_lt (lt_trans hB he))
    rw [integral_congr_ae hae, integral_const]
    simp
  · rw [capExp, if_neg hB]
    have hB0 : 0 ≤ B := not_lt.mp hB
    have hint : Integrable (fun e => min e B) expOne := by
      refine (integrable_const B).mono' ((measurable_id.min measurable_const).aestronglyMeasurable) ?_
      filter_upwards [expOne_ae_pos] with e he
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_of_lt he) hB0)]
      exact min_le_right e B
    have hnonneg : 0 ≤ᵐ[expOne] fun e => min e B := by
      filter_upwards [expOne_ae_pos] with e he
      exact le_min (le_of_lt he) hB0
    rw [hint.integral_eq_integral_Ioc_meas_le hnonneg (Filter.Eventually.of_forall fun e => min_le_right e B)]
    have htail : ∀ u ∈ Ioc 0 B, expOne.real {e : ℝ | u ≤ min e B} = Real.exp (-u) := by
      intro u hu
      have hset : {e : ℝ | u ≤ min e B} = Ici u := by
        ext e
        simp only [mem_ofPred_eq, le_min_iff, mem_Ici, and_iff_left hu.2]
      rw [hset, ← measureReal_congr (Ioi_ae_eq_Ici (μ := expOne))]
      have hcompl := measureReal_compl (μ := expOne) (s := Iic u) measurableSet_Iic
      have hcdf : expOne.real (Iic u) = 1 - Real.exp (-u) := by
        rw [expOne_real_Iic, if_pos (le_of_lt hu.1)]
      change expOne.real (Ioi u) = Real.exp (-u)
      rw [← compl_Iic, hcompl, probReal_univ, hcdf]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc htail, ← intervalIntegral.integral_of_le hB0]
    have hc : Continuous (fun u : ℝ => Real.exp (-u)) := by fun_prop
    have hderiv : ∀ u ∈ uIcc (0 : ℝ) B, HasDerivAt (fun w : ℝ => -Real.exp (-w)) (Real.exp (-u)) u := by
      intro u _
      have h1 : HasDerivAt (fun w : ℝ => -w) (-1) u := (hasDerivAt_id u).neg
      have h2 := h1.exp.neg
      have hrew : -(Real.exp (-u) * -1) = Real.exp (-u) := by ring
      exact hrew ▸ h2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable 0 B)
    rw [hftc]
    simp
    ring

lemma qComp_eq_capExp (t h : ℝ) :
    qComp t h = capExp ((h + 1) * (Real.exp (1 - t) - 1)) := by
  unfold qComp
  rw [compTraj_eq]
  have hrew : (h + 1) * Real.exp (1 - t) - 1 - h = (h + 1) * (Real.exp (1 - t) - 1) := by ring
  rw [hrew, integral_min_expOne]

lemma hasDerivAt_capExp_nonneg {B : ℝ} (hB : 0 ≤ B) :
    HasDerivAt capExp (Real.exp (-B)) B := by
  rcases lt_or_eq_of_le hB with hpos | rfl
  · have hfn : HasDerivAt (fun w : ℝ => 1 - Real.exp (-w)) (Real.exp (-B)) B := by
      have h1 : HasDerivAt (fun w : ℝ => -w) (-1) B := (hasDerivAt_id B).neg
      have h2 := h1.exp.const_sub 1
      have hrew : -(Real.exp (-B) * -1) = Real.exp (-B) := by ring
      exact hrew ▸ h2
    refine hfn.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hpos] with w hw
    have hnw : ¬ w < 0 := not_lt.mpr (le_of_lt hw)
    simp [capExp, hnw]
  · simp only [neg_zero, Real.exp_zero]
    rw [← hasDerivWithinAt_univ, ← Iic_union_Ici (a := (0 : ℝ))]
    refine HasDerivWithinAt.union ?_ ?_
    · refine (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr ?_ (by simp [capExp])
      intro w hw
      rcases lt_or_eq_of_le (mem_Iic.mp hw) with hlt | rfl
      · simp [capExp, hlt]
      · simp [capExp]
    · have hfn : HasDerivAt (fun w : ℝ => 1 - Real.exp (-w)) 1 0 := by
        have h1 : HasDerivAt (fun w : ℝ => -w) (-1) (0 : ℝ) := (hasDerivAt_id 0).neg
        simpa using h1.exp.const_sub 1
      refine hfn.hasDerivWithinAt.congr ?_ (by simp [capExp])
      intro w hw
      have hnw : ¬ w < 0 := not_lt.mpr hw
      simp [capExp, hnw]

lemma hasDerivAt_qComp_t {t h : ℝ} (ht1 : t ≤ 1) (hh : 0 ≤ h) :
    HasDerivAt (fun t' => qComp t' h)
      (-(h + 1) * Real.exp (1 - t) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))) t := by
  have he : 0 ≤ Real.exp (1 - t) - 1 := by
    linarith [Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)]
  have hB : 0 ≤ (h + 1) * (Real.exp (1 - t) - 1) := mul_nonneg (by linarith) he
  have hinner : HasDerivAt (fun t' => (h + 1) * (Real.exp (1 - t') - 1))
      (-(h + 1) * Real.exp (1 - t)) t := by
    have h1 : HasDerivAt (fun t' => 1 - t') (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h2 := (h1.exp.sub_const 1).const_mul (h + 1)
    have hrew : (h + 1) * (Real.exp (1 - t) * -1) = -(h + 1) * Real.exp (1 - t) := by ring
    exact hrew ▸ h2
  have hcomp := (hasDerivAt_capExp_nonneg hB).comp t hinner
  have hrew : Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) * (-(h + 1) * Real.exp (1 - t)) =
      -(h + 1) * Real.exp (1 - t) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) := by ring
  exact (hrew ▸ hcomp).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t' => qComp_eq_capExp t' h)

lemma hasDerivAt_qComp_h {t h : ℝ} (ht1 : t ≤ 1) (hh : 0 ≤ h) :
    HasDerivAt (fun h' => qComp t h')
      ((Real.exp (1 - t) - 1) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))) h := by
  have he : 0 ≤ Real.exp (1 - t) - 1 := by
    linarith [Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)]
  have hB : 0 ≤ (h + 1) * (Real.exp (1 - t) - 1) := mul_nonneg (by linarith) he
  have hinner : HasDerivAt (fun h' => (h' + 1) * (Real.exp (1 - t) - 1))
      (Real.exp (1 - t) - 1) h := by
    simpa using ((hasDerivAt_id h).add_const 1).mul_const (Real.exp (1 - t) - 1)
  have hcomp := (hasDerivAt_capExp_nonneg hB).comp h hinner
  have hrew : Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) * (Real.exp (1 - t) - 1) =
      (Real.exp (1 - t) - 1) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) := by ring
  exact (hrew ▸ hcomp).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun h' => qComp_eq_capExp t h')

end AuxLemma43

open OptStochMatch.Tight AuxLemma43

theorem solution (t h : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 ≤ h) :
    DifferentiableAt ℝ (fun t' => qComp t' h) t ∧
    DifferentiableAt ℝ (fun h' => qComp t h') h ∧
    DifferentiableAt ℝ (fun t' => qComp t' 0) t ∧
    deriv (fun t' => qComp t' h) t +
        (h + 1) * (1 + deriv (fun h' => qComp t h') h - qComp t h) = 0 ∧
    0 ≤ 1 + deriv (fun h' => qComp t h') h - qComp t h ∧
    1 + deriv (fun h' => qComp t h') h - qComp t h ≤ -deriv (fun t' => qComp t' 0) t := by
  have _ := ht0
  have hdt := hasDerivAt_qComp_t ht1 hh
  have hdh := hasDerivAt_qComp_h ht1 hh
  have hdt0 := hasDerivAt_qComp_t ht1 (le_refl (0 : ℝ))
  have he : 0 ≤ Real.exp (1 - t) - 1 := by
    linarith [Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)]
  have hB : ¬ (h + 1) * (Real.exp (1 - t) - 1) < 0 :=
    not_lt.mpr (mul_nonneg (by linarith) he)
  have hq : qComp t h = 1 - Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) := by
    rw [qComp_eq_capExp, capExp, if_neg hB]
  have hsens : 1 + deriv (fun h' => qComp t h') h - qComp t h =
      Real.exp (1 - t) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) := by
    rw [hdh.deriv, hq]
    ring
  refine ⟨hdt.differentiableAt, hdh.differentiableAt, hdt0.differentiableAt, ?_, ?_, ?_⟩
  · rw [hsens, hdt.deriv]
    ring
  · rw [hsens]
    exact le_of_lt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  · rw [hsens, hdt0.deriv]
    have hexp_le : -((h + 1) * (Real.exp (1 - t) - 1)) ≤ -((0 + 1) * (Real.exp (1 - t) - 1)) := by
      nlinarith [mul_nonneg hh he]
    have hle := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (le_of_lt (Real.exp_pos (1 - t)))
    linarith
