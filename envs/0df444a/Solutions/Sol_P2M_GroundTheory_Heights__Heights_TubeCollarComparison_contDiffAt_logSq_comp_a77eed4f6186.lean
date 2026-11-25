-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeCollarComparison_contDiffAt_logSq_comp_a77eed4f6186
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:27.914918+00:00
-- url     : https://prove2.me/submissions/56787ee0-c1d4-4e5b-af16-55bb319423ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeCollarCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_analyticAt_eval_3f0f1a9d1eb0


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeCollarComparison
namespace GroundTheory.Heights₂.Heights.TubeCollarComparison
theorem _root_.solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (Fin m) ℂ)
    (x : Fin n → ℂ) (hP : eval (A *ᵥ x) P ≠ 0) :
    ContDiffAt ℝ 2 (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) x := by
  have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) (A *ᵥ x) :=
    (((TubeFormComparison.analyticAt_eval P _).contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
  have hv : ContDiffAt ℝ 2 (logAbsSq P) (A *ᵥ x) := h1.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hP))
  have hA : ContDiff ℝ 2 (fun x : Fin n → ℂ => A *ᵥ x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  exact ((hv.comp x hA.contDiffAt).pow 2).div_const 2
end GroundTheory.Heights₂.Heights.TubeCollarComparison
