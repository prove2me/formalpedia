-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_varInt_congr_875943a43ccc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:25.411819+00:00
-- url     : https://prove2.me/submissions/6dafeaa4-c76e-4861-ad47-131d00e6be59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {d : ℕ} {f g : (Fin n → ℂ) → ℝ}
    (h : ∀ x ∈ ComplexSets.zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs
  · rw [CutOffDominated.chartDens_congr_zeroSet h]
  · rfl
end GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit
