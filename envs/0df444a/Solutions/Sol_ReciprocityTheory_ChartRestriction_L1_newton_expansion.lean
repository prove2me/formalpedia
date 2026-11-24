-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.newton_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:47.173827+00:00
-- url     : https://prove2.me/submissions/5fee8213-11ed-44b9-9ae4-11b9a8bf503a

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
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ k : K, ‖k‖ ≤ 1 ∧ P.eval (x + y) = P.eval x + P.derivative.eval x * y + k * y ^ 2 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Q ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨k, k.2, ?_⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q (⟨x, hx⟩ + ⟨y, hy⟩)
  have e2 := newton_eval_ball Q ⟨x, hx⟩
  have e3 := newton_eval_ball (Polynomial.derivative Q) ⟨x, hx⟩
  rw [Polynomial.derivative_map]
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at h e1 e2 e3
  rw [e1, e2, e3, h]
end ReciprocityTheory.ChartRestriction.L1
