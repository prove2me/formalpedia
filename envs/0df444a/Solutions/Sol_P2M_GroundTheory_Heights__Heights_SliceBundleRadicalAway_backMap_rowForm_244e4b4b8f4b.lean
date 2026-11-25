-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_rowForm_244e4b4b8f4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:23.037311+00:00
-- url     : https://prove2.me/submissions/ee3e6b3b-2d61-400b-b841-65ba7dd303f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653

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
theorem _root_.solution (i : Fin d) : backMap J d q k (rowForm J d q k i) = 0 := by
  simp only [rowForm, map_sum, map_mul, backMap, eval₂Hom_X', eval₂Hom_C, baseToTot_toBase]
  rw [← toTot_eq_zero J d q k (x := ∑ j, C (X (i, j)) * (X j - C (C (q j))))
    (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))]
  simp [map_sum, map_mul, map_sub]
end GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
