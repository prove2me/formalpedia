-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.PT.l2_sum_eq_sum_norm_sq_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:04.899962+00:00
-- url     : https://prove2.me/submissions/d978af8e-a4d4-447c-8f5f-b2cfc6db1c59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_integrableOn_fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_continuous_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2.PT
theorem _root_.solution {n : ℕ} (q : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → (Fin n → Vsp X.dim) → ℂ) (he : ∀ i ∈ s, Continuous (e i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → X.l2ip q (e i) (e j) = 0) :
    X.l2 q (fun v => ∑ i ∈ s, c i * e i v) = ∑ i ∈ s, ‖c i‖ ^ 2 * X.l2 q (e i) := by
  classical
  have hwc := X.continuous_weight q n
  have hpt : ∀ (G : (Fin n → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim), X.ptN2 q G v =
      (G v * (starRingEnd ℂ) (G v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)).re := by
    intro G v
    simp only [PT.ptN2]
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hint : ∀ G H : (Fin n → Vsp X.dim) → ℂ, Continuous G → Continuous H →
      MeasureTheory.IntegrableOn (fun v => G v * (starRingEnd ℂ) (H v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)) (X.fd n) :=
    fun G H hG hH => X.integrableOn_fd ((hG.mul (Complex.continuous_conj.comp hH)).mul hwc)
  have hA : ∀ G : (Fin n → Vsp X.dim) → ℂ, Continuous G → X.l2 q G = (X.l2ip q G G).re := by
    intro G hG
    simp only [PT.l2, PT.l2ip, MeasureTheory.setAverage_eq]
    simp_rw [hpt G]
    rw [Complex.smul_re]
    congr 1
    first
      | exact integral_re (hint G G hG hG)
      | simpa using integral_re (hint G G hG hG)
  have hsum_int : ∀ v : Fin n → Vsp X.dim,
      (∑ i ∈ s, c i * e i v) * (starRingEnd ℂ) (∑ i ∈ s, c i * e i v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) *
        (e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)) := by
    intro v
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have hterm : ∀ i ∈ s, ∀ j ∈ s, MeasureTheory.IntegrableOn (fun v => (c i * (starRingEnd ℂ) (c j)) *
      (e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ))) (X.fd n) :=
    fun i hi j hj => (hint (e i) (e j) (he i hi) (he j hj)).const_mul _
  have hB : ∫ v in X.fd n, (∑ i ∈ s, c i * e i v) * (starRingEnd ℂ) (∑ i ∈ s, c i * e i v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) *
        ∫ v in X.fd n, e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by
    simp_rw [hsum_int]
    rw [MeasureTheory.integral_finset_sum _ fun i hi =>
      MeasureTheory.integrable_finset_sum _ fun j hj => hterm i hi j hj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finset_sum _ fun j hj => hterm i hi j hj]
    refine Finset.sum_congr rfl fun j _ => ?_
    first
      | exact MeasureTheory.integral_const_mul _ _
      | exact MeasureTheory.integral_mul_left _ _
  have hF : Continuous (fun v => ∑ i ∈ s, c i * e i v) :=
    continuous_finset_sum _ fun i hi => continuous_const.mul (he i hi)
  have hip : X.l2ip q (fun v => ∑ i ∈ s, c i * e i v) (fun v => ∑ i ∈ s, c i * e i v) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * X.l2ip q (e i) (e j) := by
    simp only [PT.l2ip, MeasureTheory.setAverage_eq]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    first
      | (simp only [Complex.real_smul]; ring)
      | rw [mul_smul_comm]
  have hdiag : ∀ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * X.l2ip q (e i) (e j) =
      (c i * (starRingEnd ℂ) (c i)) * X.l2ip q (e i) (e i) := by
    intro i hi
    refine Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => absurd hi h)
    rw [horth i hi j hj (Ne.symm hji), mul_zero]
  rw [hA _ hF, hip, Finset.sum_congr rfl hdiag, Complex.re_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hA _ (he i hi), Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
end ReciprocityTheory.ChartRestriction.G.I2.PT
