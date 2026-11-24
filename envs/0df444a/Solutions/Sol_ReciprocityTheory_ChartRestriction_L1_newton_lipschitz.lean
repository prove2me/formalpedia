-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.newton_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:48.745533+00:00
-- url     : https://prove2.me/submissions/039e72ef-3312-4b3f-8ab0-0a2107e74b32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_exists_poly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_eval_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.evalSubFactor Q ⟨x, hx⟩ ⟨y, hy⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q ⟨x, hx⟩
  have e2 := newton_eval_ball Q ⟨y, hy⟩
  simp only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h e1 e2
  rw [e1, e2, h, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) k.2
end ReciprocityTheory.ChartRestriction.L1
