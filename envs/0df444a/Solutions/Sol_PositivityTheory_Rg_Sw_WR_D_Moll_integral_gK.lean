-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.integral_gK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:50.608483+00:00
-- url     : https://prove2.me/submissions/d4410a8e-71af-45e6-bd51-04ffc273dbb6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution : ∫ v, gK (n := n) v = 1 := by
  have h1 : ∫ s : ℝ, (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2) = 1 := by
    rw [integral_const_mul]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  unfold gK
  rw [integral_fintype_prod_volume_eq_prod (f := fun _ (w : Fin n → ℝ) =>
    ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))]
  simp_rw [integral_fintype_prod_volume_eq_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)), h1,
    Finset.prod_const_one]
end PositivityTheory.Rg.Sw.WR.D.Moll
