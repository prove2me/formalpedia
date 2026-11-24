-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_eval_poly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:34.110299+00:00
-- url     : https://prove2.me/submissions/01108534-3ba1-4d56-82dc-b122925cd289

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ

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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : ℕ} {σ : Type*} (p : MvPolynomial σ ℂ)
    {γ : (Fin D → ℂ) → σ → ℂ} {u : Fin D → ℂ} (hγ : ∀ i, AnalyticAt ℂ (fun v => γ v i) u) :
    AnalyticAt ℂ (fun v => eval (γ v) p) u := by
  induction p using MvPolynomial.induction_on
  · simpa using analyticAt_const
  · rename_i p q hp hq
    have h := hp.add hq
    simp only [map_add]
    exact h
  · rename_i p i hp
    have h := hp.mul (hγ i)
    simp only [map_mul, MvPolynomial.eval_X]
    exact h
end ReciprocityTheory.ChartRestriction.G.Geo
