-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_cauchy1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:23:50.665498+00:00
-- url     : https://prove2.me/submissions/67a2473c-7f2d-4895-bc03-9a11dc3eda8d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {H : EuclideanSpace ℂ ι → ℂ} (hH : Differentiable ℂ H) (y : EuclideanSpace ℂ ι)
    (j : ι) {M : ℝ} (hM : ∀ t : ℂ, ‖t‖ = 1 → ‖H (y + t • EuclideanSpace.single j 1)‖ ≤ M) :
    ‖fderiv ℂ H y (EuclideanSpace.single j 1)‖ ≤ M := by
  set g : ℂ → ℂ := fun t => H (y + t • EuclideanSpace.single j 1) with hgdef
  have hl : HasDerivAt (fun t : ℂ => y + t • EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (EuclideanSpace.single j (1 : ℂ))).const_add y
  have hg : Differentiable ℂ g := fun t =>
    (hH _).comp t (differentiableAt_const _ |>.add (differentiableAt_id.smul_const _))
  have hd : deriv g 0 = fderiv ℂ H y (EuclideanSpace.single j 1) := by
    have h2 := (hH (y + (0 : ℂ) • EuclideanSpace.single j 1)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hl
    simp only [zero_smul, add_zero] at h2
    exact h2.deriv
  rw [← hd]
  have h3 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := g) (c := 0) (R := 1) one_pos
    hg.diffContOnCl (fun t ht => hM t (by simpa using ht))
  simpa using h3
end ReciprocityTheory.ChartRestriction.G.I2
