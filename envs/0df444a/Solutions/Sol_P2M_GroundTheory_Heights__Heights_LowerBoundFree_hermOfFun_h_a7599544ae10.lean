-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_hermOfFun_h_a7599544ae10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:27.365406+00:00
-- url     : https://prove2.me/submissions/f5299546-7947-4431-8717-ec1dc03d8a29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_eq_smul_orbitRep_d4893c86613a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_prod_norm_zpow_pos_0010832a9c82

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hF : IsHomogOfDeg a F)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hpos : 0 < F z) :
    (hermOfFun ι a F).h z = F z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  set w := orbitRep z with hw
  have hP := prod_norm_zpow_pos hc a
  have hFz : F z = (∏ k, ‖c k‖ ^ a k) * F w := by rw [hzc]; exact hF c w hc
  have hRz : refNorm a z = (∏ k, ‖c k‖ ^ a k) * refNorm a w := by rw [hzc]; exact refNorm_smul a c w
  have hwz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [hzc]
    simp [torusSmul, h0]
  have hFw : 0 < F w := by
    rw [hFz] at hpos
    exact pos_of_mul_pos_right hpos hP.le
  have hRw := refNorm_pos a hwz
  show refNorm a z * Real.exp (Real.log (F w / refNorm a w)) = F z
  rw [Real.exp_log (div_pos hFw hRw), hRz, hFz]
  field_simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
