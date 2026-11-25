-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isWeightedHomogeneous_pderiv_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:27.176941+00:00
-- url     : https://prove2.me/submissions/a1ef5112-2a9e-4a68-b788-bc3dfb6ed183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA

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
theorem _root_.solution {σ : Type*} {w : σ → ℤ} {f : MvPolynomial σ R} {d : ℤ}
    (h : IsWeightedHomogeneous w f d) (q : σ) :
    IsWeightedHomogeneous w (pderiv q f) (d - w q) := by
  classical
  intro m hm
  rw [coeff_pderiv] at hm
  have h1 : coeff (m + Finsupp.single q 1) f ≠ 0 := fun h0 => hm (by rw [h0, zero_mul])
  have h2 := h h1
  rw [map_add] at h2
  have h3 : Finsupp.weight w (Finsupp.single q 1) = w q := by
    rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul]
  rw [h3] at h2
  linarith
end ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
