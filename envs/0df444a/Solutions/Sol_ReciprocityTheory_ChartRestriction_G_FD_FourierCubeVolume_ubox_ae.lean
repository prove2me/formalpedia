-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.ubox_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:42.277781+00:00
-- url     : https://prove2.me/submissions/a4ca21c3-012a-48ce-8a05-1a0ac55fde62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
theorem _root_.solution (N : ℕ) : (I2.DimB.ubox N) =ᵐ[volume] cube N := by
  have h1 : I2.DimB.ubox N = Set.pi Set.univ (fun i => Ioc ((0 : Fin N → ℝ) i) ((1 : Fin N → ℝ) i)) := by
    ext x
    simp [I2.DimB.ubox]
  have h2 : cube N = Set.Icc (0 : Fin N → ℝ) 1 := by
    rw [cube, ← Set.pi_univ_Icc]
    rfl
  rw [h1, h2]
  exact Measure.univ_pi_Ioc_ae_eq_Icc
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
