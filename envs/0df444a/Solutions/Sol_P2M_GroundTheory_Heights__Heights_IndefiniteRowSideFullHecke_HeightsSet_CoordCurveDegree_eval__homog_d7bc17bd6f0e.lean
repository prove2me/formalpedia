-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_eval__homog_d7bc17bd6f0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:19.516014+00:00
-- url     : https://prove2.me/submissions/b835ed94-9a3a-498c-863d-525cb589c8b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
theorem _root_.solution {L : Type*} [Field L] (f : ℚ →+* L) (d : ∀ k, ι k) (N : ℕ)
    (g : MvPolynomial (Σ k, ι k) ℚ) (hN : ∀ m ∈ g.support, ∀ k, blockDeg m k ≤ N)
    (w : (Σ k, ι k) → L) (hw : ∀ k, w ⟨k, d k⟩ ≠ 0) :
    eval₂ f w (homog d N g) = (∏ k, w ⟨k, d k⟩ ^ N) * eval₂ f (fun p ↦ w p / w ⟨p.1, d p.1⟩) g := by
  conv_rhs => rw [g.as_sum]
  rw [homog, eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [eval₂_mul, eval₂_monomial, eval₂_monomial, eval₂_prod]
  simp only [eval₂_pow, eval₂_X, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  have h1 : ∏ p, (w p / w ⟨p.1, d p.1⟩) ^ m p =
      (∏ p, w p ^ m p) / ∏ k, w ⟨k, d k⟩ ^ blockDeg m k := by
    simp only [div_pow, Finset.prod_div_distrib, blockDeg]
    congr 1
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun k _ ↦ Finset.prod_pow_eq_pow_sum (s := Finset.univ)
      (f := fun i ↦ m ⟨k, i⟩) (a := w ⟨k, d k⟩)
  have h2 : ∏ k, w ⟨k, d k⟩ ^ N =
      (∏ k, w ⟨k, d k⟩ ^ (N - blockDeg m k)) * ∏ k, w ⟨k, d k⟩ ^ blockDeg m k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [← pow_add, Nat.sub_add_cancel (hN m hm k)]
  have h3 : ∏ k, w ⟨k, d k⟩ ^ blockDeg m k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)
  rw [h1, h2]
  field_simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
