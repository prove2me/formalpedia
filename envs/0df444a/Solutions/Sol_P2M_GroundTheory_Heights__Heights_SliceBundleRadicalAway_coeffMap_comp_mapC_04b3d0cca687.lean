-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:50.234673+00:00
-- url     : https://prove2.me/submissions/d86f32a7-a3db-47bc-8e87-9d347924d4af

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
theorem _root_.solution :
    (solveMap J d q k).comp (MvPolynomial.map C) = C.comp (toBase J q k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [solveMap, coeffMap]
  · intro j
    simp [solveMap]
end GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
