-- Prove2me | solution 1 for OptStochMatch.Tight.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:32:01.515031+00:00
-- url     : https://prove2.me/submissions/0cef620c-d8f1-425d-8cbc-96740ca67a29

import Definitions.Def_OptStochMatch_Tight_Comparison

namespace AuxProp42

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

lemma integral_min_expOne_of_nonneg {B : ℝ} (hB : 0 ≤ B) :
    (∫ e, min e B ∂expOne) = 1 - Real.exp (-B) := by
  have hint : Integrable (fun e => min e B) expOne := by
    refine (integrable_const B).mono' ((measurable_id.min measurable_const).aestronglyMeasurable) ?_
    filter_upwards [expOne_ae_pos] with e he
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_of_lt he) hB)]
    exact min_le_right e B
  have hnonneg : 0 ≤ᵐ[expOne] fun e => min e B := by
    filter_upwards [expOne_ae_pos] with e he
    exact le_min (le_of_lt he) hB
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
  rw [setIntegral_congr_fun measurableSet_Ioc htail, ← intervalIntegral.integral_of_le hB]
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

end AuxProp42

open OptStochMatch.Tight AuxProp42

theorem solution :
    (∀ t h : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h →
      qComp t h = 1 - Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))) ∧
    (∀ h : ℝ, 0 ≤ h → qComp 1 h = 0) ∧
    qComp 0 0 = 1 - Real.exp (1 - Real.exp 1) := by
  have hmain : ∀ t h : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h →
      qComp t h = 1 - Real.exp (-((h + 1) * (Real.exp (1 - t) - 1))) := by
    intro t h _ ht1 hh
    unfold qComp
    rw [compTraj_eq]
    have hrew : (h + 1) * Real.exp (1 - t) - 1 - h = (h + 1) * (Real.exp (1 - t) - 1) := by ring
    rw [hrew]
    have he : 0 ≤ Real.exp (1 - t) - 1 := by
      linarith [Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)]
    exact integral_min_expOne_of_nonneg (mul_nonneg (by linarith) he)
  refine ⟨hmain, ?_, ?_⟩
  · intro h hh
    rw [hmain 1 h zero_le_one le_rfl hh]
    simp
  · rw [hmain 0 0 le_rfl zero_le_one le_rfl]
    congr 2
    ring
