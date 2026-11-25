-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_volume_cube_3a64e2ae9337
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:39.622448+00:00
-- url     : https://prove2.me/submissions/b230d399-ccec-42f6-80ed-9c7be62bef96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_cube_eq_a38c3022fb97

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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (cube n c) = ENNReal.ofReal ((2 * c) ^ n) := by
  rw [cube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  ring_nf
end GroundTheory.Heights₂.Heights.KShort
