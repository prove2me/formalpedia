-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:23.082518+00:00
-- url     : https://prove2.me/submissions/3a01551f-fc1e-4576-9f3c-d0996ab40ed3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_mConeMap_weightedHomogeneousComponent_ec0138e761d8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ))
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hf ⊢
  rw [mConeMap_weightedHomogeneousComponent, hf, map_zero]
end GroundTheory.Heights₂.Heights.OrbitCurve
