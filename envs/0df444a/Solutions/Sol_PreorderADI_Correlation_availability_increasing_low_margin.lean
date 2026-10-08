-- Prove2me | solution 1 for PreorderADI.Correlation.availability_increasing_low_margin
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:42:29.508416+00:00
-- url     : https://prove2.me/submissions/8776e2b5-bbbf-4f22-a8b2-106dba002a7a

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace PADIfc

open PreorderADI.Correlation

lemma N_Iio_eq_Iic (t : ℝ) :
    (gaussianReal 0 1).real (Set.Iio t) = (gaussianReal 0 1).real (Set.Iic t) := by
  have hs : (gaussianReal (0:ℝ) 1) {t} = 0 :=
    (gaussianReal_absolutelyContinuous (0:ℝ) (v := 1) one_ne_zero) (Real.volume_singleton)
  simp only [measureReal_def]
  rw [measure_congr (Iio_ae_eq_Iic' hs)]

lemma Phi_eq_Iio (t : ℝ) : stdNormalCdf t = (gaussianReal 0 1).real (Set.Iio t) := by
  rw [N_Iio_eq_Iic, stdNormalCdf, cdf_eq_real]

lemma Phi_strictMono : StrictMono stdNormalCdf := by
  intro a b hab
  rw [stdNormalCdf, stdNormalCdf, cdf_eq_real, cdf_eq_real]
  have hU : Set.Iic b = Set.Iic a ∪ Set.Ioc a b := (Set.Iic_union_Ioc_eq_Iic hab.le).symm
  rw [hU, measureReal_union (Set.disjoint_left.2 (fun x hx hx' => by
      simp only [Set.mem_Iic, Set.mem_Ioc] at hx hx'; linarith)) measurableSet_Ioc]
  have hpos : 0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
    rw [measureReal_def]
    refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    intro h0
    have := (gaussianReal_absolutelyContinuous' (0:ℝ) (v := 1) one_ne_zero) h0
    rw [Real.volume_Ioc] at this
    simp at this
    linarith
  linarith

lemma Phi_zero : stdNormalCdf 0 = 1 / 2 := by
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have h1 : (gaussianReal 0 1).real (Set.Ioi (0:ℝ)) = (gaussianReal 0 1).real (Set.Iio 0) := by
    conv_lhs => rw [← hneg]
    rw [measureReal_def, measureReal_def, Measure.map_apply measurable_neg measurableSet_Ioi]
    congr 2
    ext x
    simp
  have h2 : (gaussianReal 0 1).real (Set.Iic (0:ℝ))ᶜ = 1 - (gaussianReal 0 1).real (Set.Iic 0) :=
    probReal_compl_eq_one_sub measurableSet_Iic
  rw [Set.compl_Iic, h1, N_Iio_eq_Iic] at h2
  rw [stdNormalCdf, cdf_eq_real]
  linarith

lemma key (a b σ : ℝ) (v : NNReal) (hσ : 0 < σ) (hv : b ^ 2 + (v : ℝ) = σ ^ 2) :
    ∫ x, (gaussianReal 0 v).real {w | w < a + b * x} ∂(gaussianReal 0 1)
      = stdNormalCdf (a / σ) := by
  set μ := gaussianReal (0:ℝ) 1 with hμ
  set ν := gaussianReal (0:ℝ) v with hν
  set S : Set (ℝ × ℝ) := {p | p.2 - b * p.1 < a} with hS
  have hSm : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have hsec : ∀ x : ℝ, {w : ℝ | w < a + b * x} = Prod.mk x ⁻¹' S := by
    intro x
    ext w
    simp only [hS, Set.mem_preimage]
    show w < a + b * x ↔ w - b * x < a
    constructor <;> intro h <;> linarith
  have h1 : ∫ x, ν.real {w | w < a + b * x} ∂μ = ((μ.prod ν) S).toReal := by
    simp_rw [hsec, measureReal_def]
    rw [Measure.prod_apply hSm, integral_toReal]
    · exact (measurable_measure_prodMk_left hSm).aemeasurable
    · exact Filter.Eventually.of_forall (fun x => measure_lt_top _ _)
  let g : ℝ → ℝ := fun x => (-b) * x
  let f : ℝ × ℝ → ℝ := fun p => (-b) * p.1 + p.2
  have hf : Measurable f := by fun_prop
  have h2 : (μ.prod ν) S = ((μ.prod ν).map f) (Set.Iio a) := by
    rw [Measure.map_apply hf measurableSet_Iio]
    congr 1
    ext p
    simp only [hS, Set.mem_preimage, Set.mem_Iio, f]
    show p.2 - b * p.1 < a ↔ -b * p.1 + p.2 < a
    constructor <;> intro h <;> linarith
  have h3 : (μ.prod ν).map f = (μ.map g).conv ν := by
    calc (μ.prod ν).map f
        = ((μ.prod ν).map (Prod.map g id)).map (fun p : ℝ × ℝ => p.1 + p.2) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
      _ = ((μ.map g).prod (ν.map id)).map (fun p : ℝ × ℝ => p.1 + p.2) := by
          rw [Measure.map_prod_map μ ν (by fun_prop) measurable_id]
      _ = (μ.map g).conv ν := by
          rw [Measure.map_id]
          rfl
  have h4 : (μ.map g).conv ν = μ.map (fun x => σ * x) := by
    rw [hμ, hν, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal,
      gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
      rw [neg_sq]
      linarith
  rw [h1, h2, h3, h4, Measure.map_apply (by fun_prop) measurableSet_Iio, Phi_eq_Iio,
    measureReal_def]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio]
  rw [lt_div_iff₀ hσ, mul_comm]

lemma avail_eq (P : Params) (hP : P.Standing) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    availability P ρ = stdNormalCdf (P.lamL + 2 * P.zL * Real.sqrt (1 - ρ ^ 2)) := by
  have hσ := hP.sigmaL_pos
  have hsq : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hv : (ρ * P.sigmaL) ^ 2 + ((Real.toNNReal (lowSd P ρ ^ 2) : NNReal) : ℝ)
      = P.sigmaL ^ 2 := by
    rw [Real.coe_toNNReal _ (sq_nonneg _), lowSd]
    rw [show (P.sigmaL * Real.sqrt (1 - ρ ^ 2)) ^ 2 = P.sigmaL ^ 2 * Real.sqrt (1 - ρ ^ 2) ^ 2 by ring,
      hsq]
    ring
  have hpt : ∀ x, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x}
      = (gaussianReal 0 (Real.toNNReal (lowSd P ρ ^ 2))).real
          {w | w < (P.muL + 2 * P.zL * lowSd P ρ) + (ρ * P.sigmaL) * x} := by
    intro x
    rw [lowDemandLaw, ← zero_add (lowMean P ρ x), ← gaussianReal_map_add_const, measureReal_def,
      measureReal_def, Measure.map_apply (measurable_add_const _)
        (measurableSet_lt (by fun_prop) measurable_const)]
    congr 2
    ext w
    simp only [Set.mem_preimage]
    show (w + lowMean P ρ x) / 2 < orderQty P ρ x ↔
      w < (P.muL + 2 * P.zL * lowSd P ρ) + (ρ * P.sigmaL) * x
    simp only [orderQty, lowMean]
    constructor <;> intro h <;> linarith
  unfold availability
  simp_rw [hpt]
  rw [key _ _ P.sigmaL _ hσ hv]
  congr 1
  unfold Params.lamL lowSd
  field_simp

end PADIfc

open PreorderADI.Correlation in
theorem solution (P : Params) (hP : P.Standing)
    (h2c : P.vL < 2 * P.c) :
    P.zL < 0 ∧ StrictMonoOn (availability P) (Set.Ico (0:ℝ) 1) := by
  have hvL : 0 < P.vL := hP.c_pos.trans hP.c_lt_vL
  have hz : P.zL < 0 := by
    by_contra h
    have hm := (monotone_cdf (gaussianReal 0 1)) (not_lt.1 h)
    have e := hP.zL_spec
    have e0 := PADIfc.Phi_zero
    unfold stdNormalCdf at e e0
    rw [e, e0, le_div_iff₀ hvL] at hm
    linarith
  refine ⟨hz, ?_⟩
  intro a ha b hb hab
  rw [PADIfc.avail_eq P hP a ha.1 ha.2, PADIfc.avail_eq P hP b hb.1 hb.2]
  apply PADIfc.Phi_strictMono
  have hb1 : 0 ≤ 1 - b ^ 2 := by nlinarith [hb.1, hb.2]
  have hlt : Real.sqrt (1 - b ^ 2) < Real.sqrt (1 - a ^ 2) :=
    Real.sqrt_lt_sqrt hb1 (by nlinarith [ha.1])
  nlinarith
