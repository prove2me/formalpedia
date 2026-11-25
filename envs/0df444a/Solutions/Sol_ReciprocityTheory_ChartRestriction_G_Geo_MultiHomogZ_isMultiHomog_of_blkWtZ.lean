-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isMultiHomog_of_blkWtZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:19.398527+00:00
-- url     : https://prove2.me/submissions/1fd4b601-e99e-47dc-b505-436bca96791e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_weight_blkWtZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
theorem _root_.solution {f : MRingOver R ι} {n : K → ℤ}
    (h : ∀ k, IsWeightedHomogeneous (blkWtZ (ι := ι) k) f (n k)) :
    IsMultiHomog f (fun k => (n k).toNat) := by
  intro m hm k
  have e := h k (mem_support_iff.mp hm)
  rw [weight_blkWtZ, ← Nat.cast_sum] at e
  show _ = (n k).toNat
  rw [← e, Int.toNat_natCast]
end ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
