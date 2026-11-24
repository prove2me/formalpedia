-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_eval_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:33.774042+00:00
-- url     : https://prove2.me/submissions/3a87b715-7c74-41fe-9bf0-c37063dc7a7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → (Σ k, ι k) → ℂ} {y : E} (hF : ∀ p, AnalyticAt ℂ (fun y => F y p) y) (f : MRing ι) :
    AnalyticAt ℂ (fun y => eval (F y) (map (Int.castRingHom ℂ) f)) y := by
  induction (map (Int.castRingHom ℂ) f) using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hF i)
end ReciprocityTheory.ChartRestriction.G.Geo
