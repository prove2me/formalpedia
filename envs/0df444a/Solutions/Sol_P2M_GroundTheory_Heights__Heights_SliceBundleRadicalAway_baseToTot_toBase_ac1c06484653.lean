-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:49.966291+00:00
-- url     : https://prove2.me/submissions/56816cb0-f19d-4e14-a6fe-5066e6f7f2de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway

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
open GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)
namespace GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
theorem _root_.solution (a : MvPolynomial (Fin n) ℂ) :
    baseToTot J d q k (toBase J q k a) = toTot J d q k (MvPolynomial.map C a) := by
  simp [baseToTot, toBase, quotToTot]
end GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
