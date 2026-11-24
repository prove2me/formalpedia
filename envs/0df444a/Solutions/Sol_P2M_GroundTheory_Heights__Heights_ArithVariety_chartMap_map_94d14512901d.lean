-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_map_94d14512901d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:43.586004+00:00
-- url     : https://prove2.me/submissions/d0d9edec-51c0-4930-9c06-7672d545071f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
variable (c : (k : ι) → Fin (n k + 1))
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) :
    P.chartMap c (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom _) (P.chartCoord c) f := by
  rw [chartMap, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _
end GroundTheory.Heights₂.Heights.ArithVariety
