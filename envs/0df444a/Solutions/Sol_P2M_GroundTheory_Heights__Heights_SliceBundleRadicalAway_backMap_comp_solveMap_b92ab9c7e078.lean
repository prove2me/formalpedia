-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_comp_solveMap_b92ab9c7e078
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:22.655934+00:00
-- url     : https://prove2.me/submissions/73aea04b-8d36-42a4-a17a-0e549740e2e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_rowForm_244e4b4b8f4b

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
theorem _root_.solution : (backMap J d q k).comp (solveMap J d q k) = toTot J d q k := by
  have hc : (backMap J d q k).comp (coeffMap J d q k) = (toTot J d q k).comp C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coeffMap, backMap, baseToTot_toBase]
    · intro ij
      simp only [RingHom.comp_apply, coeffMap, eval₂Hom_X', map_sub]
      split_ifs
      · rw [map_mul, backMap_rowForm, mul_zero, sub_zero]
        simp [backMap]
      · simp [backMap]
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [solveMap] using RingHom.congr_fun hc a
  · intro j
    simp [solveMap, backMap, baseToTot_toBase]
end GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
