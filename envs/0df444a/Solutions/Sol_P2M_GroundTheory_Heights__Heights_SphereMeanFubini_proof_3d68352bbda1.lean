-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanFubini_proof_3d68352bbda1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:47.936178+00:00
-- url     : https://prove2.me/submissions/c75d4011-7dd8-4314-9de6-055eb72a6329

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_consEquiv_apply_f1f52a18dac4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_measurePreserving_consEquiv_fe40b3b8d4c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_preimage_ballProd_fbe88fcf28b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_nrmGroups_consGroup_5b3e998146ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ballProd_pos_bf80568889a6


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
open MeasureTheory Measure Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanFubini
namespace GroundTheory.Heights₂.Heights.SphereMeanFubini
theorem _root_.solution : SphereMeanFubini.Statement := by
  intro n k h G hG
  have hmp := measurePreserving_consEquiv (n := n) k
  have hme := (consEquiv (n := n) k).measurableEmbedding
  have hpre := preimage_ballProd h k
  set H : (Fin n → ℂ) × (Fin k × Fin n → ℂ) → ℝ :=
    fun p => G (nrmGroups h (k + 1) (consEquiv k p)) with hH
  have hHi : IntegrableOn H (ballH h ×ˢ ballProd h k) (volume.prod volume) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hme (f := fun u => G (nrmGroups h (k + 1) u))).2 hG
  have hint : ∫ p in ballH h ×ˢ ballProd h k, H p ∂(volume.prod volume) =
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb hme (fun u => G (nrmGroups h (k + 1) u)) _
  have hvol : volume (ballProd h (k + 1)) = volume (ballH h) * volume (ballProd h k) := by
    rw [← hmp.measure_preimage_equiv, hpre, Measure.volume_eq_prod, Measure.prod_prod]
  rw [IntegrableOn, ← Measure.prod_restrict] at hHi
  rw [← Measure.prod_restrict, integral_prod _ hHi] at hint
  have hB0 : (volume (ballProd h k)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(volume_ballProd_pos h k).ne', (volume_ballProd_lt_top h k).ne⟩
  have hinner : ∀ v, sphereMean h k (fun w => G (consGroup (nrmv h v) w)) =
      (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) := by
    intro v
    simp only [hH, consEquiv_apply, nrmGroups_consGroup]
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  have hfun : (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) =
      fun v => (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) :=
    funext hinner
  have hlhs : sphereMean h (k + 1) G = (volume (ballProd h (k + 1))).toReal⁻¹ *
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHi.integral_prod_left.const_mul _
  · rw [hlhs, ← hint, hvol, setAverage_eq, smul_eq_mul, measureReal_def, hfun, integral_const_mul,
      ENNReal.toReal_mul, mul_inv]
    ring
end GroundTheory.Heights₂.Heights.SphereMeanFubini
