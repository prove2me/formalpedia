-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_analyticAt_eval_map_2cf0cf611716
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:15.333793+00:00
-- url     : https://prove2.me/submissions/ef552948-f5d3-4b6c-93a7-273ecfb6e7e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSimpleRootBranch
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_map_eval_eq_sum_bb3ac0c02484

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) v := by
  have h : (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) =
      fun v => ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v; exact eval_map_eval_eq_sum p v.1 v.2
  rw [h]
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ) _ fun i _ => ?_
  refine AnalyticAt.mul ?_ (analyticAt_snd.pow i)
  exact (AnalyticOnNhd.eval_mvPolynomial (p.coeff i) v.1 trivial).comp analyticAt_fst
end GroundTheory.Heights₂.Heights.ComplexSets
