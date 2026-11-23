-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:50.535301+00:00
-- url     : https://prove2.me/submissions/84a8333c-092b-4aa9-97f3-de166bb1406f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ)
    (x : W) : polyDeriv (∑ i ∈ s, P i) u F x = ∑ i ∈ s, polyDeriv (P i) u F x := by
  exact map_sum (AddMonoidHom.mk' (fun Q : MvPolynomial σ ℂ => polyDeriv Q u F x)
    (fun Q R => polyDeriv_add Q R u F x)) P s
end ReciprocityTheory.ChartRestriction.G.I2
