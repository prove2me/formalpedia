-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.totalDegree_pderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:43.891515+00:00
-- url     : https://prove2.me/submissions/129bf386-70ba-4adf-87c0-0366b212a5ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (i : σ) (Q : MvPolynomial σ k) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree - 1 := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    have h1 := MvPolynomial.le_totalDegree hs
    have h2 : s = (s - Finsupp.single i 1) + Finsupp.single i 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))).symm
    have h3 : (s.sum fun _ e => e) = ((s - Finsupp.single i 1).sum fun _ e => e) + 1 := by
      conv_lhs => rw [h2]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have h4 : ((s - Finsupp.single i 1).sum fun _ => id) = ((s - Finsupp.single i 1).sum fun _ e => e) := rfl
    have h5 : (s.sum fun _ => id) = (s.sum fun _ e => e) := rfl
    omega
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
