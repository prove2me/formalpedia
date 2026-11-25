-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_eval__mul_blk_9a6df9c2595d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:59:27.893792+00:00
-- url     : https://prove2.me/submissions/285886eb-3cef-4bc3-8fde-692d786b0e83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution {S : Type*} [CommRing S] {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d)
    (f : ℤ →+* S) (g : (Σ k, ι k) → S) (t : K → S) :
    eval₂ f (fun q => g q * t q.1) s = (∏ k, t k ^ d k) * eval₂ f g s := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ q, (g q * t q.1) ^ m q = (∏ k, t k ^ d k) * ∏ q, g q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [hprod]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagPull
