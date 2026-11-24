-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:32.365812+00:00
-- url     : https://prove2.me/submissions/13c1ac29-cad4-4c18-98e1-fcdd3d1801e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x))
    (k : ι) (i : Fin (n k + 1)) (hi : v (coordVec x k i) < ⨆ j, v (coordVec x k j)) :
    (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∈ orbitCenter x v := by
  refine Ideal.subset_span ⟨coordDeg n ⟨k, i⟩, (geoMultiHomog_iff _ _).mpr
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, i⟩), ?_⟩
  simpa [evalCone, coordDeg, Pi.single_apply, pow_ite] using hi
end GroundTheory.Heights₂.Heights
