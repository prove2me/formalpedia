-- Prove2me | solution 1 for SysRiskPortfolio.CoER.eq_A4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:09:47.521084+00:00
-- url     : https://prove2.me/submissions/e09e2b83-8670-417d-aff5-c6d44846be60

import Mathlib
import Theorems.Thm_SysRiskPortfolio_CoER_eq_A3
import Theorems.Thm_SysRiskPortfolio_CoER_covar_display

open MeasureTheory ProbabilityTheory SysRiskPortfolio.CoER Set Filter Topology

namespace GaussAux

lemma Phi_mono : Monotone Phi := monotone_cdf _

lemma Phi_cont : Continuous Phi := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono : Monotone Phi := Phi_mono
  have hsing : (cdf (gaussianReal 0 1)).measure {a} = 0 := by
    rw [measure_cdf]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_singleton a
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hl : Function.leftLim Phi a = Phi a := by
    apply le_antisymm (hmono.leftLim_le le_rfl)
    have : cdf (gaussianReal 0 1) a - Function.leftLim (cdf (gaussianReal 0 1)) a ≤ 0 := hsing
    unfold Phi at *
    linarith
  have hr : ContinuousWithinAt Phi (Ici a) a := (cdf (gaussianReal 0 1)).right_continuous' a
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, hr⟩
  rw [← continuousWithinAt_Iio_iff_Iic]
  exact hmono.continuousWithinAt_Iio_iff_leftLim_eq.2 hl

lemma gauss_Iic (μ : ℝ) (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    gaussianReal μ v (Iic x) = ENNReal.ofReal (Phi ((x - μ) / Real.sqrt v)) := by
  set s := Real.sqrt v with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hmap : gaussianReal μ v = (gaussianReal 0 1).map (fun z => s * z + μ) := by
    have e := Measure.map_map (μ := gaussianReal 0 1) (measurable_add_const μ)
      (measurable_const_mul s)
    rw [show (fun z => s * z + μ) = (fun z => z + μ) ∘ (fun z => s * z) from rfl, ← e,
      gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · ring
    · ext; simp [hs, Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun z => s * z + μ) ⁻¹' Iic x = Iic ((x - μ) / s) := by
    ext z; simp only [mem_preimage, mem_Iic]; rw [le_div_iff₀ hspos]; constructor <;> intro h <;> linarith
  rw [hpre, ← ofReal_cdf]; rfl

lemma Phi_atTop : Tendsto Phi atTop (𝓝 1) := tendsto_cdf_atTop _
lemma Phi_atBot : Tendsto Phi atBot (𝓝 0) := tendsto_cdf_atBot _

lemma A_nonempty {q : ℝ} (hq : q < 1) : {t : ℝ | q ≤ Phi t}.Nonempty := by
  obtain ⟨T, hT⟩ := (eventually_ge_atTop (α := ℝ) 0).and
    (Phi_atTop.eventually (lt_mem_nhds hq)) |>.exists
  exact ⟨T, hT.2.le⟩

lemma A_bdd {q : ℝ} (hq : 0 < q) : BddBelow {t : ℝ | q ≤ Phi t} := by
  obtain ⟨T, hT⟩ := eventually_atBot.mp (Phi_atBot.eventually (gt_mem_nhds hq))
  refine ⟨T, fun t ht => ?_⟩
  by_contra h
  push Not at h
  have := hT t h.le
  simp only [mem_setOf_eq] at ht
  linarith

lemma Phi_PhiInv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : Phi (PhiInv q) = q := by
  have hne := A_nonempty hq1
  have hbdd := A_bdd hq0
  have hclosed : IsClosed {t : ℝ | q ≤ Phi t} := isClosed_le continuous_const Phi_cont
  have hmem : PhiInv q ∈ {t : ℝ | q ≤ Phi t} := hclosed.csInf_mem hne hbdd
  apply le_antisymm _ hmem
  -- for t < PhiInv q, Phi t < q
  have hlt : ∀ t < PhiInv q, Phi t < q := by
    intro t ht
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h) (not_le.mpr ht)
  have hc := Phi_cont.continuousAt (x := PhiInv q)
  have : Tendsto Phi (𝓝[<] (PhiInv q)) (𝓝 (Phi (PhiInv q))) := hc.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto this (eventually_nhdsWithin_of_forall (fun t ht => (hlt t ht).le))

lemma VaR_gauss (μ : ℝ) (v : NNReal) (hv : v ≠ 0) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    VaR (gaussianReal μ v) q = μ + Real.sqrt v * PhiInv q := by
  set s := Real.sqrt v with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hset : {x : ℝ | ENNReal.ofReal q ≤ gaussianReal μ v (Iic x)}
      = (fun t => μ + s * t) '' {t : ℝ | q ≤ Phi t} := by
    ext x
    simp only [mem_setOf_eq, mem_image, gauss_Iic μ v hv x]
    have hP : (0:ℝ) ≤ Phi ((x - μ) / s) := cdf_nonneg _ _
    rw [← hs, ENNReal.ofReal_le_ofReal_iff hP]
    constructor
    · intro h; exact ⟨(x - μ) / s, h, by field_simp; ring⟩
    · rintro ⟨t, ht, rfl⟩
      convert ht using 2; field_simp; ring
  unfold VaR PhiInv
  rw [hset]
  have hmono : Monotone (fun t : ℝ => μ + s * t) := fun a b h => by
    simp only; nlinarith
  exact (hmono.map_csInf_of_continuousAt (by fun_prop) (A_nonempty hq1) (A_bdd hq0)).symm

lemma VaR_gauss' (μ σ : ℝ) (hσ : 0 < σ) (v : NNReal) (hv : (v : ℝ) = σ ^ 2) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) : VaR (gaussianReal μ v) q = μ + σ * PhiInv q := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv; nlinarith
  rw [VaR_gauss μ v hv0 hq0 hq1, hv, Real.sqrt_sq hσ.le]

/-- Lower-tail first moment of a Gaussian, by the fundamental theorem of calculus. -/
lemma tail_mean (M s : ℝ) (hs : 0 < s) (v : NNReal) (hv : (v : ℝ) = s ^ 2) (a : ℝ) :
    ∫ x in Iic (M + s * a), x ∂(gaussianReal M v) = M * Phi a - s * phi a := by
  have hvpos : (0 : ℝ) < v := by rw [hv]; positivity
  have hv0 : v ≠ 0 := by intro h; rw [h] at hvpos; simp at hvpos
  set c := M + s * a with hc
  set p := gaussianPDFReal M v with hp
  have hpdef : ∀ x, p x = (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - M) ^ 2 / (2 * v)) :=
    fun x => rfl
  -- convert to a Lebesgue integral
  have h1 : ∫ x in Iic c, x ∂(gaussianReal M v) = ∫ x in Iic c, p x * x := by
    rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
      integral_gaussianReal_eq_integral_smul hv0]
    congr 1; funext x
    by_cases hx : x ∈ Iic c <;> simp [hx, smul_eq_mul, hp]
  -- integrability
  set b : ℝ := 1 / (2 * v) with hb
  have hbpos : 0 < b := by positivity
  have hpint : Integrable p := integrable_gaussianPDFReal M v
  have hqint : Integrable (fun x => (x - M) * p x) := by
    have := ((integrable_mul_exp_neg_mul_sq hbpos).comp_sub_right M).const_mul
      (Real.sqrt (2 * Real.pi * v))⁻¹
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only [hpdef, hb]
    rw [show -(x - M) ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * v)) * (x - M) ^ 2 by ring]
    ring
  -- antiderivative
  set F : ℝ → ℝ := fun x => -(v : ℝ) * p x with hF
  have hFd : ∀ x, HasDerivAt F ((x - M) * p x) x := by
    intro x
    have h0 : HasDerivAt (fun x => -(x - M) ^ 2 / (2 * (v : ℝ))) (-(2 * (x - M)) / (2 * v)) x := by
      have := (((hasDerivAt_id x).sub_const M).pow 2).neg.div_const (2 * (v : ℝ))
      refine this.congr_deriv ?_
      simp only [id, Nat.cast_ofNat, pow_one, mul_one]
      norm_num
    have h2 := (h0.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹).const_mul (-(v : ℝ))
    have e : (x - M) * p x = -(v : ℝ) * ((Real.sqrt (2 * Real.pi * v))⁻¹ *
        (Real.exp (-(x - M) ^ 2 / (2 * (v : ℝ))) * (-(2 * (x - M)) / (2 * (v : ℝ))))) := by
      rw [hpdef]; field_simp
    rw [e]; exact h2
  have hFlim : Tendsto F atBot (𝓝 0) := by
    have t1 : Tendsto (fun x : ℝ => M - x) atBot atTop :=
      tendsto_atTop_add_const_left _ M tendsto_neg_atBot_atTop
    have t2 : Tendsto (fun x : ℝ => -(x - M) ^ 2 / (2 * (v : ℝ))) atBot atBot := by
      have := ((tendsto_pow_atTop (two_ne_zero)).comp t1).atTop_div_const (by positivity : (0:ℝ) < 2 * v)
      have := tendsto_neg_atTop_atBot.comp this
      refine this.congr (fun x => ?_)
      simp only [Function.comp]; ring
    have t3 := (Real.tendsto_exp_atBot.comp t2).const_mul (-(v : ℝ) * (Real.sqrt (2 * Real.pi * v))⁻¹)
    simp only [mul_zero] at t3
    refine t3.congr (fun x => ?_)
    simp only [Function.comp, hF, hpdef]; ring
  have hFTC : ∫ x in Iic c, (x - M) * p x = F c - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto (hFd c).continuousAt.continuousWithinAt
      (fun x _ => hFd x) hqint.integrableOn hFlim
  have hsplit : ∫ x in Iic c, p x * x = M * (∫ x in Iic c, p x) + ∫ x in Iic c, (x - M) * p x := by
    have e : ∀ x, p x * x = M * p x + (x - M) * p x := fun x => by ring
    simp_rw [e]
    rw [integral_add (hpint.integrableOn.const_mul M) hqint.integrableOn, integral_const_mul]
  have hmass : ∫ x in Iic c, p x = Phi a := by
    have e := gaussianReal_apply_eq_integral M hv0 (Iic c)
    rw [gauss_Iic M v hv0, hv, Real.sqrt_sq hs.le] at e
    have e2 : (c - M) / s = a := by rw [hc]; field_simp; ring
    rw [e2] at e
    have hn : 0 ≤ ∫ x in Iic c, p x := integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _)
    have := (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) hn).mp e
    exact this.symm
  have hFc : F c = -(s * phi a) := by
    simp only [hF, hpdef, phi, gaussianPDFReal, hv, hc]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [show 2 * Real.pi * s ^ 2 = s ^ 2 * (2 * Real.pi) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hs.le]
    rw [show -(M + s * a - M) ^ 2 / (2 * s ^ 2) = -a ^ 2 / 2 by field_simp; ring]
    field_simp
  rw [h1, hsplit, hFTC, hmass, hFc]; ring

end GaussAux


open GaussAux

theorem solution (mup mum sp sm rho qm qp : ℝ) (hp : 0 < sp) (hm : 0 < sm) (hr : |rho| < 1) (hqm : 0 < qm ∧ qm < 1) (hqp : 0 < qp ∧ qp < 1) : CoER mup mum sp sm rho qm qp = mup + sp * (rho * PhiInv qm - (1 / qp) * Real.sqrt (1 - rho ^ 2) * phi (PhiInv qp)) := by
  have hr2 : 0 < 1 - rho ^ 2 := by have h := abs_lt.mp hr; nlinarith
  have h1 : VaR (gaussianReal mum ⟨sm ^ 2, sq_nonneg sm⟩) qm = mum + sm * PhiInv qm :=
    VaR_gauss' mum sm hm _ rfl hqm.1 hqm.2
  set s := sp * Real.sqrt (1 - rho ^ 2) with hsdef
  have hs : 0 < s := mul_pos hp (Real.sqrt_pos.mpr hr2)
  set M := mup + rho * sp * (mum + sm * PhiInv qm - mum) / sm with hMdef
  have hM : M = mup + rho * sp * PhiInv qm := by rw [hMdef]; field_simp; ring
  set V : NNReal := ⟨sp ^ 2 * (1 - rho ^ 2), mul_nonneg (sq_nonneg sp)
    (by have h := abs_lt.mp hr; nlinarith)⟩ with hVdef
  have hV : (V : ℝ) = s ^ 2 := by
    change sp ^ 2 * (1 - rho ^ 2) = _; rw [hsdef, mul_pow, Real.sq_sqrt hr2.le]
  have hV0 : V ≠ 0 := by
    intro h; have := congrArg (fun x : NNReal => (x : ℝ)) h; simp only [NNReal.coe_zero] at this
    rw [hV] at this; have : 0 < s ^ 2 := by positivity
    linarith
  have hlaw : condLaw mup mum sp sm rho (VaR (gaussianReal mum ⟨sm ^ 2, sq_nonneg sm⟩) qm)
      = gaussianReal M V := by
    rw [h1, eq_A3 mup mum sp sm rho _ hp hm hr]
  have hc : CoVaR mup mum sp sm rho qm qp = M + s * PhiInv qp := by
    rw [covar_display mup mum sp sm rho qm qp hp hm hr hqm hqp, hM, hsdef]
  have hPhi := Phi_PhiInv hqp.1 hqp.2
  have hint := tail_mean M s hs V hV (PhiInv qp)
  have hmeas : (gaussianReal M V (Iic (M + s * PhiInv qp))).toReal = qp := by
    rw [gauss_Iic M V hV0, hV, Real.sqrt_sq hs.le,
      show (M + s * PhiInv qp - M) / s = PhiInv qp by field_simp; ring, hPhi,
      ENNReal.toReal_ofReal hqp.1.le]
  have hq0 : qp ≠ 0 := hqp.1.ne'
  unfold CoER
  simp only []
  rw [hlaw, hc, hint, hmeas, hPhi, hM, hsdef]
  field_simp
  ring
