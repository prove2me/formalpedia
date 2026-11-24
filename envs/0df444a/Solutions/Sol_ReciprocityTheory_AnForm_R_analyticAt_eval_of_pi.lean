-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:58.940943+00:00
-- url     : https://prove2.me/submissions/25008d3f-ec7a-42ad-b5c8-0644e7332708

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*}
    {f : E → σ → ℂ} {z : E} (hf : ∀ l, AnalyticAt ℂ (f · l) z) (p : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun x => eval (f x) p) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p l hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hf l)
end ReciprocityTheory.AnForm.R
