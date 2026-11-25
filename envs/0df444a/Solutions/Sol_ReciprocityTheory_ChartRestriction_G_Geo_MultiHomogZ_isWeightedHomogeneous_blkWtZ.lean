-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isWeightedHomogeneous_blkWtZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:23.399349+00:00
-- url     : https://prove2.me/submissions/acc1b28b-e2d6-4512-8af4-2bc0d990b417

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
theorem _root_.solution {f : MRingOver R ι} {a : K → ℕ} (h : IsMultiHomog f a)
    (k : K) : IsWeightedHomogeneous (blkWtZ (ι := ι) k) f (a k : ℤ) := by
  intro d hd
  rw [weight_blkWtZ, ← h d (mem_support_iff.mpr hd) k]
  push_cast
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
