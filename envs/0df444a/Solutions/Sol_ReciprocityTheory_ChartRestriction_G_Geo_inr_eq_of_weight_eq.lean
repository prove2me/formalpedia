-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.inr_eq_of_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:47.184897+00:00
-- url     : https://prove2.me/submissions/47aad713-4cdd-4547-91db-d7b45ee322db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_sWt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (k0 : K)
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {r : ℕ} {n n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (h : Finsupp.weight (sWt k0 r) n = Finsupp.weight (sWt k0 r) n0) (k' : {k // k ≠ k0}) :
    n (Sum.inr k') = n0 (Sum.inr k') := by
  have h0 : Finsupp.weight (sWt k0 r) n k0 = Finsupp.weight (sWt k0 r) n0 k0 := by rw [h]
  have h1 : Finsupp.weight (sWt k0 r) n k'.1 = Finsupp.weight (sWt k0 r) n0 k'.1 := by rw [h]
  rw [weight_sWt_apply, weight_sWt_apply, dif_pos rfl, dif_pos rfl] at h0
  rw [weight_sWt_apply, weight_sWt_apply, dif_neg k'.2, dif_neg k'.2, Subtype.coe_eta] at h1
  omega
end ReciprocityTheory.ChartRestriction.G.Geo
