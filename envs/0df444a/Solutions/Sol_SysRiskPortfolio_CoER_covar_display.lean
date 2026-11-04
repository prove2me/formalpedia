-- Prove2me | solution 1 for SysRiskPortfolio.CoER.covar_display
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:05:52.546737+00:00
-- url     : https://prove2.me/submissions/07333366-2077-4a71-9f2c-be688a957af7

import Mathlib
import Theorems.Thm_SysRiskPortfolio_CoER_eq_A3

open MeasureTheory ProbabilityTheory SysRiskPortfolio.CoER Set Filter Topology

namespace GaussAux

lemma Phi_mono : Monotone Phi := monotone_cdf _

lemma Phi_cont : Continuous Phi := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono : Monotone Phi := Phi_mono
  have hsing : (cdf (gaussianReal 0 1)).measure {a} = 0 := by
    rw [measure_cdf]
    haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
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

end GaussAux

open GaussAux

theorem solution (mup mum sp sm rho qm qp : ℝ) (hp : 0 < sp) (hm : 0 < sm) (hr : |rho| < 1) (hqm : 0 < qm ∧ qm < 1) (hqp : 0 < qp ∧ qp < 1) : CoVaR mup mum sp sm rho qm qp = mup + rho * sp * PhiInv qm + sp * Real.sqrt (1 - rho ^ 2) * PhiInv qp := by
  have hr2 : 0 < 1 - rho ^ 2 := by have h := abs_lt.mp hr; nlinarith
  have h1 : VaR (gaussianReal mum ⟨sm ^ 2, sq_nonneg sm⟩) qm = mum + sm * PhiInv qm :=
    VaR_gauss' mum sm hm _ rfl hqm.1 hqm.2
  have hσ : 0 < sp * Real.sqrt (1 - rho ^ 2) := mul_pos hp (Real.sqrt_pos.mpr hr2)
  have h2 := VaR_gauss' (mup + rho * sp * (mum + sm * PhiInv qm - mum) / sm) _ hσ
    ⟨sp ^ 2 * (1 - rho ^ 2), mul_nonneg (sq_nonneg sp) (by have h := abs_lt.mp hr; nlinarith)⟩
    (by change sp ^ 2 * (1 - rho ^ 2) = _; rw [mul_pow, Real.sq_sqrt hr2.le]) hqp.1 hqp.2
  unfold CoVaR
  rw [h1, eq_A3 mup mum sp sm rho _ hp hm hr]
  rw [h2]
  field_simp
  ring
