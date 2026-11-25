-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:43.256884+00:00
-- url     : https://prove2.me/submissions/dc0d6ccc-fd87-4d1b-8021-de4c3d6379c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d


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
open MvPolynomial MeasureTheory Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFibreDegree
namespace GroundTheory.Heights₂.Heights.ConeFibreDegree
theorem _root_.solution {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h
end GroundTheory.Heights₂.Heights.ConeFibreDegree
