-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:57.712797+00:00
-- url     : https://prove2.me/submissions/a98180a0-52aa-45d5-918b-5899f5b4176f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (g : Polynomial ℤ) (p q : Coord n) (z : Coord n → ℂ) :
    eval z (map (Int.castRingHom ℂ) (homogForm g p q)) =
      ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : ℂ) * z p ^ j * z q ^ (g.natDegree - j) := by
  simp [homogForm, map_sum]
end GroundTheory.Heights₂.Heights
