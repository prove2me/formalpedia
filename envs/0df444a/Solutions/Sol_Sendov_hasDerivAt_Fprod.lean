-- Prove2me | solution 1 for Sendov.hasDerivAt_Fprod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:04.635076+00:00
-- url     : https://prove2.me/submissions/1342fc67-bb87-4df5-80d9-74e03627283f

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProdC_cons
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.Fprod_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a t : ℝ) : ∀ (q : Multiset ℂ),
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    have he : Fprod a 0 = fun _ : ℝ => (1 : ℂ) := by funext s; simp [Fprod]
    have hz : -(a : ℂ) * sumEraseProdC 0 id (fun v => 1 - (a : ℂ) * (t : ℂ) * v) = 0 := by simp
    rw [he, hz]
    exact hasDerivAt_const t 1
  | cons v r ih =>
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 1 - (a : ℂ) * (s : ℂ) * v) (-((a : ℂ) * v)) t := by
      simpa using ((h0.const_mul (a : ℂ)).mul_const v).const_sub 1
    have h2 := h1.mul ih
    have hfun : Fprod a (v ::ₘ r)
        = fun s : ℝ => (1 - (a : ℂ) * (s : ℂ) * v) * Fprod a r s := by
      funext s
      simp only [Fprod, Multiset.map_cons, Multiset.prod_cons]
    have hderiv : -(a : ℂ) * ((v : ℂ) * (r.map (fun w => 1 - (a : ℂ) * (t : ℂ) * w)).prod
          + (1 - (a : ℂ) * (t : ℂ) * v) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w))
        = -((a : ℂ) * v) * Fprod a r t
          + (1 - (a : ℂ) * (t : ℂ) * v)
              * (-(a : ℂ) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w)) := by
      simp only [Fprod]
      ring
    rw [hfun, sumEraseProdC_cons, id_eq, hderiv]
    exact h2
end Sendov
