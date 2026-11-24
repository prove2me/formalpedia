-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.prod_norm_update_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:00.905107+00:00
-- url     : https://prove2.me/submissions/2f957746-273e-4e65-93f2-688ffbe488d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF

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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution [DecidableEq K] (k0 : K) (v : ℂ) (a : K → ℤ) :
    ∏ k, ‖Function.update (fun _ => (1 : ℂ)) k0 v k‖ ^ a k = ‖v‖ ^ a k0 := by
  rw [Finset.prod_eq_single k0]
  · simp
  · intro k _ hk
    simp [Function.update_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ k0) h
end ReciprocityTheory.ChartRestriction.G.Geo
