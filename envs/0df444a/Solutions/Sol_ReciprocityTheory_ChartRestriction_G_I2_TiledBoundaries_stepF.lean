-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:41.601498+00:00
-- url     : https://prove2.me/submissions/697001c8-43ea-4986-8e45-af6b1cdc2d79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepF := by
  intro E _ _ X n f hf
  have hset : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
    ext v
    simp [PT.fd]
  rw [setAverage_eq, setAverage_eq, hset, volume_pi]
  first
    | simp only [measureReal_def, Measure.pi_pi, Measure.restrict_pi_pi]
    | simp only [Measure.real_def, Measure.pi_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod (f := fun _ => f)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, smul_eq_mul]
  rw [mul_pow, inv_pow]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
