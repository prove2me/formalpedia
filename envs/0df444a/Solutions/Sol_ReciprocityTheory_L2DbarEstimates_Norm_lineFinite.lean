-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.lineFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:20.054662+00:00
-- url     : https://prove2.me/submissions/e9327558-1514-485a-b429-079047f77768

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_LineFinite
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_eval_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution : lineFiniteStatement := by
  intro n Δ w h0
  have hne : MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ ≠ 0 := by
    intro hz
    apply h0
    have := eval_line n Δ w 0
    rw [hz] at this
    simpa using this.symm
  refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
  intro t ht
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_line]
  exact ht
end ReciprocityTheory.L2DbarEstimates.Norm
