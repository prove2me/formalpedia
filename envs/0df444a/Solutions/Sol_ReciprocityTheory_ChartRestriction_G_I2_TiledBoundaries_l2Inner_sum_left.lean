-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.l2Inner_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:19:44.341657+00:00
-- url     : https://prove2.me/submissions/31e92e3d-f2b6-4867-9b12-a33059774eda

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_cont_ip
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (hI : StepI) (X : PT E) (q : ℕ) {n : ℕ} {ι : Type} (t : Finset ι) (g : ι → ℂ)
    (F : ι → (Fin n → Vsp X.dim) → ℂ) (G : (Fin n → Vsp X.dim) → ℂ) (hF : ∀ j, Continuous (F j))
    (hG : Continuous G) :
    X.l2ip q (fun v => ∑ j ∈ t, g j * F j v) G = ∑ j ∈ t, g j * X.l2ip q (F j) G := by
  unfold PT.l2ip
  simp only [MeasureTheory.setAverage_eq]
  have hi : ∀ j, IntegrableOn (fun v => F j v * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) (X.fd n) :=
    fun j => hI E X n _ (cont_ip q (hF j) hG)
  have hsum : (fun v => (∑ j ∈ t, g j * F j v) * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) = fun v => ∑ j ∈ t, g j *
      (F j v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) := by
    funext v
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, MeasureTheory.integral_finset_sum _ (fun j _ => (hi j).const_mul (g j)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, mul_smul_comm]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
