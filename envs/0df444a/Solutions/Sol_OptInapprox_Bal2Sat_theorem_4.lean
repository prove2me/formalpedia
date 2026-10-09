-- Prove2me | solution 1 for OptInapprox.Bal2Sat.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T22:30:40.932546+00:00
-- url     : https://prove2.me/submissions/cffe6099-6812-4f5e-8cbc-7e13209a0989

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector
import Definitions.Def_OptInapprox_Bal2Sat_Setting

set_option autoImplicit false

section GrothSec
open MeasureTheory ProbabilityTheory Real Set

namespace GrothAux

lemma measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma abs_sign_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [Real.sign_of_neg h]
  · simp [h]
  · simp [Real.sign_of_pos h]

/-- the angular integrand -/
noncomputable def hθ (α θ : ℝ) : ℝ := Real.sign (cos θ) * Real.sign (cos (θ - α))

lemma measurable_hθ (α : ℝ) : Measurable (hθ α) := by
  unfold hθ
  exact (measurable_sign.comp continuous_cos.measurable).mul
    (measurable_sign.comp (continuous_cos.comp (continuous_id.sub continuous_const)).measurable)

lemma hθ_periodic (α : ℝ) : Function.Periodic (hθ α) π := by
  intro θ
  have h1 : cos (θ + π - α) = - cos (θ - α) := by
    rw [show θ + π - α = (θ - α) + π by ring, cos_add_pi]
  simp only [hθ, cos_add_pi, h1, Real.sign_neg]
  ring

lemma intervalIntegrable_hθ (α a b : ℝ) : IntervalIntegrable (hθ α) volume a b := by
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun (measurable_hθ α).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun θ => ?_)
  simp only [norm_one, Real.norm_eq_abs, hθ, abs_mul]
  calc |Real.sign (cos θ)| * |Real.sign (cos (θ - α))| ≤ 1 * 1 :=
        mul_le_mul (abs_sign_le _) (abs_sign_le _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma half_integral (α : ℝ) (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ∫ θ in (-(π/2))..(π/2), hθ α θ = π - 2 * α := by
  set c := α - π / 2 with hc
  have hc1 : -(π/2) ≤ c := by linarith
  have hc2 : c ≤ π/2 := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (intervalIntegrable_hθ α _ _) (intervalIntegrable_hθ α _ _)]
  have hA : ∫ θ in (-(π/2))..c, hθ α θ = ∫ θ in (-(π/2))..c, (-1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton c).ae_notMem volume] with θ hθc hmem
    rw [Set.uIoc_of_le hc1] at hmem
    have hθ' : θ < c := lt_of_le_of_ne hmem.2 (by simpa using hθc)
    have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨hmem.1, by linarith⟩
    have hcos2 : cos (θ - α) < 0 := by
      have : cos (θ - α) = - cos (θ - α + π) := by rw [cos_add_pi]; ring
      rw [this, neg_lt_zero]
      exact cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], by linarith⟩
    simp [hθ, Real.sign_of_pos hcos, Real.sign_of_neg hcos2]
  have hB : ∫ θ in c..(π/2), hθ α θ = ∫ θ in c..(π/2), (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (π/2)).ae_notMem volume] with θ hθc hmem
    rw [Set.uIoc_of_le hc2] at hmem
    have hθ' : θ < π/2 := lt_of_le_of_ne hmem.2 (by simpa using hθc)
    have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], hθ'⟩
    have hcos2 : 0 < cos (θ - α) := cos_pos_of_mem_Ioo ⟨by linarith [hmem.1], by linarith⟩
    simp [hθ, Real.sign_of_pos hcos, Real.sign_of_pos hcos2]
  rw [hA, hB]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_neg, mul_one]
  rw [hc]; ring

lemma full_integral (α : ℝ) (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ∫ θ in Ioo (-π) π, hθ α θ = 2 * π - 4 * α := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (intervalIntegrable_hθ α _ _) (intervalIntegrable_hθ α _ _)]
  have P := hθ_periodic α
  have e1 := P.intervalIntegral_add_eq (-π) (-(π/2))
  have e2 := P.intervalIntegral_add_eq 0 (-(π/2))
  rw [show -π + π = (0:ℝ) by ring, show -(π/2) + π = π/2 by ring] at e1
  rw [show (0:ℝ) + π = π by ring, show -(π/2) + π = π/2 by ring] at e2
  rw [e1, e2, half_integral α h0 hπ]
  ring

lemma radial : ∫ r in Ioi (0:ℝ), r * rexp (-(r ^ 2) / 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1/2 : ℂ)) (by norm_num)
  have h2 : (∫ r : ℝ in Ioi 0, ((r * rexp (-(r ^ 2) / 2) : ℝ) : ℂ)) = (1 : ℂ) := by
    have e : (2 * (1/2 : ℂ))⁻¹ = 1 := by norm_num
    rw [e] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    push_cast
    congr 2
    ring
  rw [integral_complex_ofReal] at h2
  exact_mod_cast h2

end GrothAux

namespace GrothAux

lemma sign_mul_of_pos {r x : ℝ} (hr : 0 < r) : Real.sign (r * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hr h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hr h)]

lemma core (α : ℝ) (h0 : 0 ≤ α) (hπ : α ≤ π) :
    ∫ p, Real.sign p.1 * Real.sign (cos α * p.1 + sin α * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 - 2 * α / π := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero 0 hv]
  rw [MeasureTheory.prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  have hm : Measurable (fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) :=
    ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun z => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top))]
  rw [← Measure.volume_eq_prod]
  rw [← integral_comp_polarCoord_symm]
  have htarget : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  have hmeas : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioo (-π) π) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [htarget]
  have key : ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioo (-π) π,
      p.1 • (((gaussianPDF 0 1 (polarCoord.symm p).1 * gaussianPDF 0 1 (polarCoord.symm p).2).toReal) •
        (Real.sign (polarCoord.symm p).1 *
          Real.sign (cos α * (polarCoord.symm p).1 + sin α * (polarCoord.symm p).2)))
      = (p.1 * rexp (-(p.1 ^ 2) / 2)) * ((2 * π)⁻¹ * hθ α p.2) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    simp only [polarCoord_symm_apply, smul_eq_mul]
    rw [ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [sign_mul_of_pos hr]
    have e1 : cos α * (r * cos θ) + sin α * (r * sin θ) = r * cos (θ - α) := by
      rw [cos_sub]; ring
    rw [e1, sign_mul_of_pos hr]
    have e2 : rexp (-(r * cos θ) ^ 2 / 2) * rexp (-(r * sin θ) ^ 2 / 2) = rexp (-(r ^ 2) / 2) := by
      rw [← Real.exp_add]; congr 1
      linear_combination (-(r ^ 2) / 2) * sin_sq_add_cos_sq θ
    have e3 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    have : (√(2 * π))⁻¹ * rexp (-(r * cos θ) ^ 2 / 2) * ((√(2 * π))⁻¹ * rexp (-(r * sin θ) ^ 2 / 2))
        = (2 * π)⁻¹ * rexp (-(r ^ 2) / 2) := by
      rw [← e2, ← e3]; ring
    rw [this]
    simp only [hθ]
    ring
  rw [setIntegral_congr_fun hmeas key]
  rw [Measure.volume_eq_prod]
  have hsp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => r * rexp (-(r ^ 2) / 2)) (fun θ : ℝ => (2 * π)⁻¹ * hθ α θ) (Ioi 0) (Ioo (-π) π)
  try simp only at hsp
  rw [hsp]
  rw [radial, integral_const_mul, full_integral α h0 hπ]
  field_simp
  ring

end GrothAux

namespace GrothAux

open HighDimProb.RandomVectors

lemma memLp_g {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (i : Fin n) : MemLp (g i) 2 P := by
  have h : MemLp id 2 (P.map (g i)) := by rw [hg.2.2 i]; exact memLp_id_gaussianReal 2
  exact h.comp_of_map (hg.1 i).aemeasurable

lemma cov_lin {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (a b : Fin n → ℝ) :
    cov[fun ω => ∑ i, g i ω * a i, fun ω => ∑ i, g i ω * b i; P] = ∑ i, a i * b i := by
  rw [covariance_fun_sum_fun_sum (fun i => (memLp_g hg i).mul_const (a i))
    (fun j => (memLp_g hg j).mul_const (b j))]
  have hcov : ∀ i j, cov[fun ω => g i ω * a i, fun ω => g j ω * b j; P]
      = if i = j then a i * b i else 0 := by
    intro i j
    rw [covariance_mul_const_left, covariance_mul_const_right]
    split_ifs with h
    · subst h
      rw [covariance_self (hg.1 i).aemeasurable]
      have : Var[g i; P] = 1 := by
        rw [← variance_id_map (hg.1 i).aemeasurable, hg.2.2 i, variance_id_gaussianReal]; simp
      rw [this]; ring
    · rw [(hg.2.1.indepFun h).covariance_eq_zero (memLp_g hg i) (memLp_g hg j)]; ring
  simp_rw [hcov]
  simp

lemma mean_lin {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (a : Fin n → ℝ) :
    ∫ ω, ∑ i, g i ω * a i ∂P = 0 := by
  rw [integral_finsetSum _ (fun i _ => ((memLp_g hg i).integrable one_le_two).mul_const (a i))]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [integral_mul_const]
  have : ∫ ω, g i ω ∂P = 0 := by
    have h := integral_map (μ := P) (hg.1 i).aemeasurable (f := id)
      measurable_id.aestronglyMeasurable
    rw [hg.2.2 i] at h
    simp only [id] at h
    rw [← h, integral_id_gaussianReal]
  rw [this, zero_mul]

end GrothAux

namespace GrothAux

open HighDimProb.RandomVectors

theorem groth_id :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {n : ℕ} (g : Fin n → Ω → ℝ), IsStandardGaussianVector P g →
      ∀ u v : Fin n → ℝ, (∑ i, (u i) ^ 2 = 1) → (∑ i, (v i) ^ 2 = 1) →
        ∫ ω, Real.sign (∑ i, g i ω * u i) * Real.sign (∑ i, g i ω * v i) ∂P =
          (2 / Real.pi) * Real.arcsin (∑ i, u i * v i) := by
  intro Ω _ P _ n g hg u v hu hv
  set ρ := ∑ i, u i * v i with hρdef
  have hρle : ρ ≤ 1 := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (u i - v i))
    have e : ∑ i, (u i - v i) ^ 2 = ∑ i, u i ^ 2 + ∑ i, v i ^ 2 - 2 * ρ := by
      rw [hρdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hu, hv] at h; linarith
  have hρge : -1 ≤ ρ := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (u i + v i))
    have e : ∑ i, (u i + v i) ^ 2 = ∑ i, u i ^ 2 + ∑ i, v i ^ 2 + 2 * ρ := by
      rw [hρdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hu, hv] at h; linarith
  set w : Fin n → ℝ := fun i => v i - ρ * u i with hw
  set X : Ω → ℝ := fun ω => ∑ i, g i ω * u i with hX
  set Z : Ω → ℝ := fun ω => ∑ i, g i ω * w i with hZ
  have hY : ∀ ω, ∑ i, g i ω * v i = ρ * X ω + Z ω := by
    intro ω
    simp only [hX, hZ, hw, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hG : HasGaussianLaw (fun ω => (g · ω)) P :=
    iIndepFun.hasGaussianLaw (fun i => ⟨by rw [hg.2.2 i]; infer_instance⟩) hg.2.1
  let L : (Fin n → ℝ) →L[ℝ] ℝ × ℝ :=
    (∑ i, u i • ContinuousLinearMap.proj i).prod (∑ i, w i • ContinuousLinearMap.proj i)
  have hXZ : HasGaussianLaw (fun ω => (X ω, Z ω)) P := by
    have h := hG.map_fun L
    have hfun : (fun ω => (X ω, Z ω)) = (fun ω => L (fun i => g i ω)) := by
      funext ω
      ext <;> simp [L, hX, hZ] <;> exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hfun]; exact h
  have huw : ∑ i, u i * w i = 0 := by
    have e : ∑ i, u i * w i = ρ - ρ * ∑ i, u i ^ 2 := by
      rw [hρdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [hw]; ring)
    rw [e, hu]; ring
  have hww : ∑ i, w i * w i = 1 - ρ ^ 2 := by
    have e : ∑ i, w i * w i = ∑ i, (v i ^ 2 - 2 * ρ * (u i * v i) + ρ ^ 2 * u i ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by simp only [hw]; ring)
    rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← hρdef, hu, hv]
    ring
  have huu : ∑ i, u i * u i = 1 := by
    rw [← hu]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hXm : AEMeasurable X P := hXZ.fst.aemeasurable
  have hZm : AEMeasurable Z P := hXZ.snd.aemeasurable
  have hind : IndepFun X Z P := by
    refine hXZ.indepFun_of_covariance_eq_zero ?_
    rw [hX, hZ, GrothAux.cov_lin hg u w, huw]
  have hXlaw : P.map X = gaussianReal 0 1 := by
    rw [hXZ.fst.map_eq_gaussianReal, ← covariance_self hXm, hX, GrothAux.cov_lin hg u u, huu,
      GrothAux.mean_lin hg u]
    simp
  set s : ℝ := Real.sin (Real.arccos ρ) with hs
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := by
    rw [hs, Real.sin_arccos, Real.sq_sqrt (by nlinarith)]
  have hZlaw : P.map Z = (gaussianReal 0 1).map (s * ·) := by
    rw [hXZ.snd.map_eq_gaussianReal, ← covariance_self hZm, hZ, GrothAux.cov_lin hg w w, hww,
      GrothAux.mean_lin hg w, gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp only [Real.coe_toNNReal', NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one, hs2]
      exact max_eq_left (by nlinarith)
  have hF : Measurable (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) :=
    (GrothAux.measurable_sign.comp measurable_fst).mul
      (GrothAux.measurable_sign.comp ((measurable_fst.const_mul ρ).add measurable_snd))
  have hcos : Real.cos (Real.arccos ρ) = ρ := Real.cos_arccos hρge hρle
  calc ∫ ω, Real.sign (∑ i, g i ω * u i) * Real.sign (∑ i, g i ω * v i) ∂P
      = ∫ ω, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) (X ω, Z ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [hY ω]
        rfl
    _ = ∫ p, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) p
          ∂(P.map (fun ω => (X ω, Z ω))) :=
        (integral_map (hXm.prodMk hZm) hF.aestronglyMeasurable).symm
    _ = ∫ p, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) p
          ∂((gaussianReal 0 1).prod ((gaussianReal 0 1).map (s * ·))) := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map hXm hZm).1 hind, hXlaw, hZlaw]
    _ = ∫ p, (fun p : ℝ × ℝ => Real.sign p.1 * Real.sign (ρ * p.1 + p.2)) p
          ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map id (s * ·))) := by
        rw [← Measure.map_prod_map _ _ measurable_id (measurable_const_mul s), Measure.map_id]
    _ = ∫ p, Real.sign p.1 * Real.sign (Real.cos (Real.arccos ρ) * p.1
          + Real.sin (Real.arccos ρ) * p.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        rw [integral_map (measurable_id.prodMap (measurable_const_mul s)).aemeasurable
          hF.aestronglyMeasurable, hcos]
        rfl
    _ = 1 - 2 * Real.arccos ρ / Real.pi :=
        GrothAux.core _ (Real.arccos_nonneg ρ) (Real.arccos_le_pi ρ)
    _ = (2 / Real.pi) * Real.arcsin ρ := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]
        field_simp
        ring

end GrothAux

end GrothSec

namespace B2Aux

open OptInapprox.Bal2Sat OptInapprox.MaxCut Finset

lemma pm_sq (b : Bool) : pm b * pm b = 1 := by cases b <;> simp [pm]

lemma pm_mul_cases (a b : Bool) : pm a * pm b = 1 ∨ pm a * pm b = -1 := by
  cases a <;> cases b <;> simp [pm]

def flipAt {n : ℕ} (j : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x j (!x j)

lemma flipAt_invol {n : ℕ} (j : Fin n) : Function.Involutive (flipAt j) := by
  intro x
  funext k
  by_cases h : k = j
  · subst h; simp [flipAt]
  · simp [flipAt, h]

lemma flipAt_same {n : ℕ} (j k : Fin n) (x : Fin n → Bool) (h : k ≠ j) : flipAt j x k = x k := by
  simp [flipAt, h]

lemma sum_flip {n : ℕ} (j : Fin n) (g : (Fin n → Bool) → ℝ)
    (h : ∀ x, g (flipAt j x) = - g x) : ∑ x, g x = 0 := by
  have e := Equiv.sum_comp (Function.Involutive.toPerm (flipAt j) (flipAt_invol j)) g
  simp only [Function.Involutive.coe_toPerm, h, Finset.sum_neg_distrib] at e
  linarith

lemma pm_flip {n : ℕ} (j : Fin n) (x : Fin n → Bool) : pm (flipAt j x j) = - pm (x j) := by
  cases h : x j <;> simp [flipAt, pm, h]

lemma sum_pm {n : ℕ} (j : Fin n) : ∑ x : Fin n → Bool, pm (x j) = 0 :=
  sum_flip j _ (fun x => pm_flip j x)

lemma sum_pm_pm {n : ℕ} (a i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * pm (x a) = if a = i then (2:ℝ) ^ n else 0 := by
  by_cases h : a = i
  · subst h; simp [pm_sq]
  · rw [if_neg h]
    refine sum_flip i _ (fun x => ?_)
    rw [pm_flip, flipAt_same i a x h]; ring

lemma sum_triple {n : ℕ} (a b i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * (pm (x a) * pm (x b)) = 0 := by
  by_cases hab : a = b
  · subst hab
    have : ∀ x : Fin n → Bool, pm (x i) * (pm (x a) * pm (x a)) = pm (x i) := by
      intro x; rw [pm_sq]; ring
    simp only [this]; exact sum_pm i
  · by_cases hia : i = a
    · subst hia
      have : ∀ x : Fin n → Bool, pm (x i) * (pm (x i) * pm (x b)) = pm (x b) := by
        intro x; rw [← mul_assoc, pm_sq]; ring
      simp only [this]; exact sum_pm b
    · by_cases hib : i = b
      · subst hib
        have : ∀ x : Fin n → Bool, pm (x i) * (pm (x a) * pm (x i)) = pm (x a) := by
          intro x; rw [mul_comm (pm (x a)), ← mul_assoc, pm_sq]; ring
        simp only [this]; exact sum_pm a
      · refine sum_flip i _ (fun x => ?_)
        rw [pm_flip, flipAt_same i a x (Ne.symm hia), flipAt_same i b x (Ne.symm hib)]; ring

lemma ind_eq {n : ℕ} (C : Literal n × Literal n) (x : Fin n → Bool) :
    (if clauseSat C x then (1:ℝ) else 0) =
      (3 - litVal C.1 x - litVal C.2 x - litVal C.1 x * litVal C.2 x) / 4 := by
  obtain ⟨⟨i, r⟩, ⟨j, s⟩⟩ := C
  simp only [clauseSat, litTrue, litVal]
  cases r <;> cases s <;> cases hx : x i <;> cases hy : x j <;> simp [pm, hx, hy] <;> norm_num

lemma satWeight_expand {n : ℕ} (I : Instance n) (x : Fin n → Bool) :
    satWeight I x = ∑ c, I.w c * ((3 - litVal (I.clause c).1 x - litVal (I.clause c).2 x
      - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4) := by
  unfold satWeight
  exact Finset.sum_congr rfl (fun c _ => by rw [ind_eq])

noncomputable def Acoef {n : ℕ} (I : Instance n) (i : Fin n) : ℝ :=
  ∑ c, I.w c * ((if (I.clause c).1.1 = i then pm (I.clause c).1.2 else 0) +
    (if (I.clause c).2.1 = i then pm (I.clause c).2.2 else 0))

lemma clause_sum {n : ℕ} (C : Literal n × Literal n) (i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * ((3 - litVal C.1 x - litVal C.2 x
      - litVal C.1 x * litVal C.2 x) / 4) =
      -((2:ℝ) ^ n / 4) * ((if C.1.1 = i then pm C.1.2 else 0) + (if C.2.1 = i then pm C.2.2 else 0)) := by
  have h : ∀ x : Fin n → Bool, pm (x i) * ((3 - litVal C.1 x - litVal C.2 x
      - litVal C.1 x * litVal C.2 x) / 4) =
      (3/4) * pm (x i) - (pm C.1.2 / 4) * (pm (x i) * pm (x C.1.1))
        - (pm C.2.2 / 4) * (pm (x i) * pm (x C.2.1))
        - (pm C.1.2 * pm C.2.2 / 4) * (pm (x i) * (pm (x C.1.1) * pm (x C.2.1))) := by
    intro x; unfold litVal; ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_pm, sum_pm_pm, sum_triple]
  split_ifs <;> simp <;> ring

lemma sum_pm_sat {n : ℕ} (I : Instance n) (i : Fin n) :
    ∑ x : Fin n → Bool, pm (x i) * satWeight I x = -((2:ℝ) ^ n / 4) * Acoef I i := by
  simp only [satWeight_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold Acoef
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h : ∀ x : Fin n → Bool, pm (x i) * (I.w c * ((3 - litVal (I.clause c).1 x
      - litVal (I.clause c).2 x - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4)) =
      I.w c * (pm (x i) * ((3 - litVal (I.clause c).1 x - litVal (I.clause c).2 x
      - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4)) := by intro x; ring
  simp only [h, ← Finset.mul_sum, clause_sum]
  ring

lemma Acoef_zero {n : ℕ} (I : Instance n) (hbal : IsBalanced I) (i : Fin n) : Acoef I i = 0 := by
  have h1 := hbal i
  have hsplit : ∑ x : Fin n → Bool, pm (x i) * satWeight I x =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), pm (x i) * satWeight I x +
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), pm (x i) * satWeight I x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin n → Bool => x i = false)]
    congr 1
    refine Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
  have hF : ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), pm (x i) * satWeight I x
      = ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), satWeight I x :=
    Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter] at hx; simp [pm, hx.2])
  have hT : ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), pm (x i) * satWeight I x
      = -∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), satWeight I x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter] at hx; simp [pm, hx.2])
  have h0 : ∑ x : Fin n → Bool, pm (x i) * satWeight I x = 0 := by
    rw [hsplit, hF, hT, h1]; ring
  rw [sum_pm_sat] at h0
  have hpos : ((2:ℝ) ^ n / 4) ≠ 0 := by positivity
  have : (-((2:ℝ) ^ n / 4)) * Acoef I i = 0 := h0
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (neg_eq_zero.1 h) hpos
  · exact h

lemma lin_zero {n : ℕ} (I : Instance n) (hbal : IsBalanced I) (x : Fin n → Bool) :
    ∑ c, I.w c * (litVal (I.clause c).1 x + litVal (I.clause c).2 x) = 0 := by
  have h : ∑ i, pm (x i) * Acoef I i = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [Acoef_zero I hbal i, mul_zero])
  unfold Acoef at h
  simp only [Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have : ∑ i, pm (x i) * (I.w c * ((if (I.clause c).1.1 = i then pm (I.clause c).1.2 else 0) +
      (if (I.clause c).2.1 = i then pm (I.clause c).2.2 else 0))) =
      I.w c * (pm (x (I.clause c).1.1) * pm (I.clause c).1.2 +
        pm (x (I.clause c).2.1) * pm (I.clause c).2.2) := by
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  rw [this]
  unfold litVal
  ring


lemma beta_bdd : BddBelow ((fun θ : ℝ => (2 + 2 / Real.pi * θ) / (3 - Real.cos θ)) ''
    Set.Icc (Real.pi / 2) Real.pi) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hp := Real.pi_pos
  have h3 : 0 < 3 - Real.cos t := by linarith [Real.cos_le_one t]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have h2 : 0 ≤ 2 + 2 / Real.pi * t := by positivity
  exact div_nonneg h2 h3.le

lemma beta_aux_le (θ : ℝ) (h1 : Real.pi / 2 ≤ θ) (h2 : θ ≤ Real.pi) :
    beta ≤ (2 + 2 / Real.pi * θ) / (3 - Real.cos θ) :=
  csInf_le beta_bdd ⟨θ, ⟨h1, h2⟩, rfl⟩

lemma beta_le_one : beta ≤ 1 := by
  have hp := Real.pi_pos
  have h := beta_aux_le (Real.pi / 2) le_rfl (by linarith)
  have : (2 + 2 / Real.pi * (Real.pi / 2)) / (3 - Real.cos (Real.pi / 2)) = 1 := by
    rw [Real.cos_pi_div_two]; field_simp; norm_num
  linarith

lemma beta_nonneg : 0 ≤ beta := by
  have hp := Real.pi_pos
  apply le_csInf
  · exact ⟨_, ⟨Real.pi / 2, ⟨le_rfl, by linarith⟩, rfl⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h3 : 0 < 3 - Real.cos t := by linarith [Real.cos_le_one t]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h2 : 0 ≤ 2 + 2 / Real.pi * t := by positivity
    exact div_nonneg h2 h3.le

lemma key_ineq (r : ℝ) (h1 : -1 ≤ r) (h2 : r ≤ 1) :
    beta * ((3 - r) / 4) ≤ (3 - 2 / Real.pi * Real.arcsin r) / 4 := by
  have hp := Real.pi_pos
  set θ := Real.arccos r with hθdef
  have hc : Real.cos θ = r := Real.cos_arccos h1 h2
  have has : Real.arcsin r = Real.pi / 2 - θ := by
    rw [hθdef, Real.arccos_eq_pi_div_two_sub_arcsin]; ring
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg r
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi r
  have hpos : 0 < 3 - r := by linarith
  have hR : 3 - 2 / Real.pi * Real.arcsin r = 2 + 2 / Real.pi * θ := by
    rw [has]; field_simp; ring
  rw [hR]
  rcases le_or_gt (Real.pi / 2) θ with h | h
  · have h' := beta_aux_le θ h hθπ
    rw [hc, le_div_iff₀ hpos] at h'
    linarith
  · have hj := Real.one_sub_mul_le_cos hθ0 h.le
    rw [hc] at hj
    have := mul_le_mul_of_nonneg_right beta_le_one hpos.le
    nlinarith

lemma dot_bounds {d : ℕ} (u w : Fin d → ℝ) (hu : ∑ k, u k ^ 2 = 1) (hw : ∑ k, w k ^ 2 = 1) :
    -1 ≤ dot u w ∧ dot u w ≤ 1 := by
  unfold dot
  constructor
  · have h := Finset.sum_nonneg (s := Finset.univ) (fun k _ => sq_nonneg (u k + w k))
    have e : ∑ k, (u k + w k) ^ 2 = ∑ k, u k ^ 2 + ∑ k, w k ^ 2 + 2 * ∑ k, u k * w k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e, hu, hw] at h; linarith
  · have h := Finset.sum_nonneg (s := Finset.univ) (fun k _ => sq_nonneg (u k - w k))
    have e : ∑ k, (u k - w k) ^ 2 = ∑ k, u k ^ 2 + ∑ k, w k ^ 2 - 2 * ∑ k, u k * w k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e, hu, hw] at h; linarith

lemma rho_bounds {n d : ℕ} (I : Instance n) (v : Fin n → Fin d → ℝ) (hv : IsUnitFamily v)
    (c : Fin I.m) :
    -1 ≤ pm (I.clause c).1.2 * pm (I.clause c).2.2 * dot (v (I.clause c).1.1) (v (I.clause c).2.1) ∧
    pm (I.clause c).1.2 * pm (I.clause c).2.2 * dot (v (I.clause c).1.1) (v (I.clause c).2.1) ≤ 1 := by
  obtain ⟨h1, h2⟩ := dot_bounds _ _ (hv (I.clause c).1.1) (hv (I.clause c).2.1)
  rcases pm_mul_cases (I.clause c).1.2 (I.clause c).2.2 with h | h <;> rw [h] <;>
    constructor <;> linarith

lemma sdpObj_le {n d : ℕ} (I : Instance n) (v : Fin n → Fin d → ℝ) (hv : IsUnitFamily v) :
    sdpObj I v ≤ ∑ c, I.w c := by
  unfold sdpObj
  apply Finset.sum_le_sum
  intro c _
  obtain ⟨h1, h2⟩ := rho_bounds I v hv c
  nlinarith [mul_nonneg (I.w_nonneg c) (sub_nonneg.2 h1)]

def vv {n : ℕ} (x : Fin n → Bool) : Fin n → Fin 1 → ℝ := fun i _ => pm (x i)

lemma pm_sq' (b : Bool) : pm b ^ 2 = 1 := by cases b <;> simp [pm]

lemma vv_unit {n : ℕ} (x : Fin n → Bool) : IsUnitFamily (vv x) := by
  intro i
  simp [vv, pm_sq']

lemma sdpObj_vv {n : ℕ} (I : Instance n) (hbal : IsBalanced I) (x : Fin n → Bool) :
    sdpObj I (vv x) = satWeight I x := by
  rw [satWeight_expand]
  have L := lin_zero I hbal x
  have key : ∀ c : Fin I.m, I.w c * ((3 - litVal (I.clause c).1 x - litVal (I.clause c).2 x
      - litVal (I.clause c).1 x * litVal (I.clause c).2 x) / 4) =
      I.w c * (3 / 4 - 1 / 4 * (pm (I.clause c).1.2 * pm (I.clause c).2.2 *
        dot (vv x (I.clause c).1.1) (vv x (I.clause c).2.1))) -
      (1 / 4) * (I.w c * (litVal (I.clause c).1 x + litVal (I.clause c).2 x)) := by
    intro c
    simp only [dot, vv, litVal, Finset.univ_unique, Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_sub_distrib, ← Finset.mul_sum, L]
  unfold sdpObj
  ring

lemma OPT_le_sdpValue {n : ℕ} (I : Instance n) (hbal : IsBalanced I) : OPT I ≤ sdpValue I := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n → Bool))
    (satWeight I)
  have h1 : OPT I = satWeight I x := hx
  rw [h1, ← sdpObj_vv I hbal x]
  apply le_csSup
  · exact ⟨∑ c, I.w c, by rintro s ⟨d, v, hv, rfl⟩; exact sdpObj_le I v hv⟩
  · exact ⟨1, vv x, vv_unit x, rfl⟩

end B2Aux


namespace B2Aux

open MeasureTheory ProbabilityTheory HighDimProb.RandomVectors OptInapprox.Bal2Sat OptInapprox.MaxCut

lemma law_lin {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (u : Fin n → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) :
    HasGaussianLaw (fun ω => ∑ i, g i ω * u i) P ∧
      P.map (fun ω => ∑ i, g i ω * u i) = gaussianReal 0 1 := by
  have hG : HasGaussianLaw (fun ω => (g · ω)) P :=
    iIndepFun.hasGaussianLaw (fun i => ⟨by rw [hg.2.2 i]; infer_instance⟩) hg.2.1
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, u i • ContinuousLinearMap.proj i
  have hX : HasGaussianLaw (fun ω => ∑ i, g i ω * u i) P := by
    have h := hG.map_fun L
    have hfun : (fun ω => ∑ i, g i ω * u i) = (fun ω => L (fun i => g i ω)) := by
      funext ω
      simp [L]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hfun]; exact h
  have hm : AEMeasurable (fun ω => ∑ i, g i ω * u i) P := hX.aemeasurable
  refine ⟨hX, ?_⟩
  have huu : ∑ i, u i * u i = 1 := by
    rw [← hu]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hX.map_eq_gaussianReal, ← covariance_self hm, GrothAux.cov_lin hg u u, huu,
    GrothAux.mean_lin hg u]
  simp

lemma sign_integral_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (u : Fin n → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) : ∫ ω, Real.sign (∑ i, g i ω * u i) ∂P = 0 := by
  obtain ⟨hX, hlaw⟩ := law_lin hg u hu
  have hm := hX.aemeasurable
  have h1 := integral_map hm (f := Real.sign) GrothAux.measurable_sign.aestronglyMeasurable
  rw [hlaw] at h1
  rw [← h1]
  have h2 : ∫ x, Real.sign x ∂gaussianReal 0 1 = ∫ x, Real.sign (-x) ∂gaussianReal 0 1 := by
    have h3 := integral_map (μ := gaussianReal 0 1) (measurable_neg.aemeasurable)
      (f := Real.sign) GrothAux.measurable_sign.aestronglyMeasurable
    have e : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
      simpa using gaussianReal_map_neg (μ := 0) (v := 1)
    rw [e] at h3
    exact h3
  simp only [Real.sign_neg, integral_neg] at h2
  linarith

lemma ae_ne {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {g : Fin n → Ω → ℝ} (hg : IsStandardGaussianVector P g) (u : Fin n → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) : ∀ᵐ ω ∂P, ∑ i, g i ω * u i ≠ 0 := by
  obtain ⟨hX, hlaw⟩ := law_lin hg u hu
  have hm := hX.aemeasurable
  have h0 : P {ω | ∑ i, g i ω * u i = 0} = 0 := by
    have h := Measure.map_apply_of_aemeasurable hm (measurableSet_singleton (0:ℝ))
    rw [hlaw] at h
    have hz : gaussianReal 0 1 {0} = 0 :=
      gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)
    rw [hz] at h
    exact h.symm
  rw [ae_iff]
  simpa using h0

lemma integral_clause {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (sa sb : Ω → ℝ) (A B C : ℝ) (ha : Integrable sa P) (hb : Integrable sb P)
    (hp : Integrable (fun ω => sa ω * sb ω) P) :
    ∫ ω, (3 / 4 - A * sa ω - B * sb ω - C * (sa ω * sb ω)) ∂P =
      3 / 4 - A * ∫ ω, sa ω ∂P - B * ∫ ω, sb ω ∂P - C * ∫ ω, sa ω * sb ω ∂P := by
  have i0 : Integrable (fun _ : Ω => (3 / 4 : ℝ)) P := integrable_const _
  have i1 : Integrable (fun ω => 3 / 4 - A * sa ω) P := i0.sub (ha.const_mul A)
  have i2 : Integrable (fun ω => 3 / 4 - A * sa ω - B * sb ω) P := i1.sub (hb.const_mul B)
  rw [integral_sub i2 (hp.const_mul C), integral_sub i1 (hb.const_mul B),
    integral_sub i0 (ha.const_mul A), integral_const_mul, integral_const_mul, integral_const_mul]
  simp

lemma integrable_of_bdd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (h : ∀ ω, |f ω| ≤ 1) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using h ω))

end B2Aux

open OptInapprox.Bal2Sat OptInapprox.MaxCut MeasureTheory HighDimProb.RandomVectors in
theorem solution {n : ℕ} (I : Instance n) (hbal : IsBalanced I)
    (ε : ℝ) (hε : 0 ≤ ε) {d : ℕ} (v : Fin n → Fin d → ℝ) (hv : IsUnitFamily v)
    (hnear : sdpValue I - ε ≤ sdpObj I v)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Fin d → Ω → ℝ) (hg : IsStandardGaussianVector P g) :
    Integrable (fun ω => satWeight I (round v (fun k => g k ω))) P ∧
      beta * (OPT I - ε) ≤ ∫ ω, satWeight I (round v (fun k => g k ω)) ∂P := by
  obtain ⟨X, hX⟩ : ∃ X : Fin n → Ω → ℝ, ∀ i ω, X i ω = ∑ k, g k ω * v i k :=
    ⟨fun i ω => ∑ k, g k ω * v i k, fun _ _ => rfl⟩
  have hXm : ∀ i, Measurable (X i) := by
    intro i
    have : X i = fun ω => ∑ k, g k ω * v i k := funext (hX i)
    rw [this]
    exact Finset.measurable_sum _ (fun k _ => (hg.1 k).mul_const _)
  have hsm : ∀ i, Measurable (fun ω => Real.sign (X i ω)) :=
    fun i => GrothAux.measurable_sign.comp (hXm i)
  have hint1 : ∀ i, Integrable (fun ω => Real.sign (X i ω)) P :=
    fun i => B2Aux.integrable_of_bdd (hsm i) (fun ω => GrothAux.abs_sign_le _)
  have hint2 : ∀ i j, Integrable (fun ω => Real.sign (X i ω) * Real.sign (X j ω)) P := by
    intro i j
    refine B2Aux.integrable_of_bdd ((hsm i).mul (hsm j)) (fun ω => ?_)
    rw [abs_mul]
    have h1 := GrothAux.abs_sign_le (X i ω)
    have h2 := GrothAux.abs_sign_le (X j ω)
    nlinarith [abs_nonneg (Real.sign (X i ω)), abs_nonneg (Real.sign (X j ω))]
  have hE1 : ∀ i, ∫ ω, Real.sign (X i ω) ∂P = 0 := by
    intro i
    have := B2Aux.sign_integral_zero hg (v i) (hv i)
    simpa only [hX] using this
  have hE2 : ∀ i j, ∫ ω, Real.sign (X i ω) * Real.sign (X j ω) ∂P =
      2 / Real.pi * Real.arcsin (dot (v i) (v j)) := by
    intro i j
    have := GrothAux.groth_id P g hg (v i) (v j) (hv i) (hv j)
    simpa only [hX, dot] using this
  have hne : ∀ᵐ ω ∂P, ∀ i, X i ω ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have := B2Aux.ae_ne hg (v i) (hv i)
    filter_upwards [this] with ω hω
    rw [hX]; exact hω
  -- the clause integrand
  let F : Fin I.m → Ω → ℝ := fun c ω =>
    3 / 4 - (pm (I.clause c).1.2 / 4) * Real.sign (X (I.clause c).1.1 ω)
      - (pm (I.clause c).2.2 / 4) * Real.sign (X (I.clause c).2.1 ω)
      - (pm (I.clause c).1.2 * pm (I.clause c).2.2 / 4) *
        (Real.sign (X (I.clause c).1.1 ω) * Real.sign (X (I.clause c).2.1 ω))
  have hFint : ∀ c, Integrable (F c) P := by
    intro c
    have i0 : Integrable (fun _ : Ω => (3 / 4 : ℝ)) P := integrable_const _
    exact ((i0.sub ((hint1 _).const_mul _)).sub ((hint1 _).const_mul _)).sub
      ((hint2 _ _).const_mul _)
  have hae : ∀ᵐ ω ∂P, satWeight I (round v (fun k => g k ω)) = ∑ c, I.w c * F c ω := by
    filter_upwards [hne] with ω hω
    have hpm : ∀ i, pm (round v (fun k => g k ω) i) = Real.sign (X i ω) := by
      intro i
      have hd : dot (fun k => g k ω) (v i) = X i ω := by rw [hX]; rfl
      have h0 := hω i
      simp only [OptInapprox.Bal2Sat.round, hd]
      rcases lt_or_gt_of_ne h0 with h | h
      · simp [pm, h, Real.sign_of_neg h]
      · simp [pm, not_lt.2 h.le, Real.sign_of_pos h]
    rw [B2Aux.satWeight_expand]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [litVal, hpm, F]
    ring_nf
  have hsumint : Integrable (fun ω => ∑ c, I.w c * F c ω) P :=
    integrable_finsetSum _ (fun c _ => (hFint c).const_mul _)
  have hintegrable : Integrable (fun ω => satWeight I (round v (fun k => g k ω))) P :=
    hsumint.congr (hae.mono (fun ω h => h.symm))
  refine ⟨hintegrable, ?_⟩
  have hI1 : ∫ ω, satWeight I (round v (fun k => g k ω)) ∂P = ∑ c, I.w c *
      (3 / 4 - (pm (I.clause c).1.2 * pm (I.clause c).2.2 / 4) *
        (2 / Real.pi * Real.arcsin (dot (v (I.clause c).1.1) (v (I.clause c).2.1)))) := by
    rw [integral_congr_ae hae, integral_finsetSum _ (fun c _ => (hFint c).const_mul _)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [integral_const_mul]
    congr 1
    simp only [F]
    rw [B2Aux.integral_clause _ _ _ _ _ (hint1 _) (hint1 _) (hint2 _ _), hE1, hE1, hE2]
    ring
  have hsdp : beta * sdpObj I v ≤ ∑ c, I.w c *
      (3 / 4 - (pm (I.clause c).1.2 * pm (I.clause c).2.2 / 4) *
        (2 / Real.pi * Real.arcsin (dot (v (I.clause c).1.1) (v (I.clause c).2.1)))) := by
    unfold sdpObj
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun c _ => ?_)
    obtain ⟨h1, h2⟩ := B2Aux.rho_bounds I v hv c
    have hk := B2Aux.key_ineq _ h1 h2
    have hσ := B2Aux.pm_mul_cases (I.clause c).1.2 (I.clause c).2.2
    have hs : Real.arcsin (pm (I.clause c).1.2 * pm (I.clause c).2.2 *
        dot (v (I.clause c).1.1) (v (I.clause c).2.1)) =
        pm (I.clause c).1.2 * pm (I.clause c).2.2 *
          Real.arcsin (dot (v (I.clause c).1.1) (v (I.clause c).2.1)) := by
      rcases hσ with h | h <;> rw [h] <;> simp [Real.arcsin_neg]
    rw [hs] at hk
    have hw := I.w_nonneg c
    have : beta * (I.w c * (3 / 4 - 1 / 4 * (pm (I.clause c).1.2 * pm (I.clause c).2.2 *
        dot (v (I.clause c).1.1) (v (I.clause c).2.1)))) =
        I.w c * (beta * ((3 - pm (I.clause c).1.2 * pm (I.clause c).2.2 *
        dot (v (I.clause c).1.1) (v (I.clause c).2.1)) / 4)) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hw
    nlinarith [hk]
  have hobj : OPT I - ε ≤ sdpObj I v := by
    have := B2Aux.OPT_le_sdpValue I hbal
    linarith
  rw [hI1]
  calc beta * (OPT I - ε) ≤ beta * sdpObj I v :=
        mul_le_mul_of_nonneg_left hobj B2Aux.beta_nonneg
    _ ≤ _ := hsdp
