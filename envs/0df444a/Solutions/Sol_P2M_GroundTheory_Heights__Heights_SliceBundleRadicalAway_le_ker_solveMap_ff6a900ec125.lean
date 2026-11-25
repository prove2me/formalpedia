-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_le_ker_solveMap_ff6a900ec125
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:25.470676+00:00
-- url     : https://prove2.me/submissions/d98f17b8-9ac0-427f-b4b7-05ecfefd4e7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_solveMap_gen_3170fbd5da3a

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
theorem _root_.solution : universalSliceIdeal J d q ≤ RingHom.ker (solveMap J d q k) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, coeffMap_comp_mapC]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact solveMap_gen J d q k i
end GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
