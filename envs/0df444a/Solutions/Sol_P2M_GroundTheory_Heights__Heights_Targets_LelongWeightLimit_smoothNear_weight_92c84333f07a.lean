-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_smoothNear_weight_92c84333f07a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:04.334221+00:00
-- url     : https://prove2.me/submissions/774791d3-9003-4124-81a7-f20b0480e45e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)
open GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit
theorem _root_.solution {Z : Set (Fin n → ℂ)} (u : Fin n → ℂ) {k : (Fin n → ℂ) → ℝ}
    (hk : SmoothNear Z k) (hk0 : ∀ x ∈ Z, 0 < k x) {ε : ℝ} (hε : 0 < ε) :
    SmoothNear Z (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) := by
  obtain ⟨U, hU, hZU, hkU⟩ := hk
  refine ⟨U ∩ k ⁻¹' Ioi 0, hkU.continuousOn.isOpen_inter_preimage hU isOpen_Ioi,
    fun x hx => ⟨hZU hx, hk0 x hx⟩, ?_⟩
  refine ContDiffOn.div_const (ContDiffOn.log ?_ fun x hx => ?_) _
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).contDiffOn.add
      (contDiffOn_const.mul ((hkU.mono inter_subset_left).pow 2))
  · have h1 : 0 < ε * k x ^ 2 := mul_pos hε (pow_pos hx.2 2)
    have h2 : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
    exact (by linarith : (0 : ℝ) < ‖linEval u x‖ ^ 2 + ε * k x ^ 2).ne'
end GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit
