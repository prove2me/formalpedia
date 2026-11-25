-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.cube_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:23.050741+00:00
-- url     : https://prove2.me/submissions/6004e1d3-039c-4f12-859d-a25e2b156f78

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
theorem _root_.solution (N : ℕ) : MeasurableSet (cube N) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
