-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cube_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:20.377998+00:00
-- url     : https://prove2.me/submissions/ff01fdd2-af77-47b3-8121-fa65eeee5549

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cubeIco_eq

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (κ : Type) [Fintype κ] :
    cubeIco κ =ᵐ[volume] {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} := by
  have h2 : {x : κ → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1 := by
    ext x; simp [Set.mem_pi]
  rw [cubeIco_eq, h2]
  exact (Measure.univ_pi_Ico_ae_eq_Icc).trans (Measure.univ_pi_Ioc_ae_eq_Icc).symm
end ReciprocityTheory.ChartRestriction.G.I2
