-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.totalDegree_pderiv_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:02.189626+00:00
-- url     : https://prove2.me/submissions/d293897e-1128-4d8e-82f6-e55d74fbfc26

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {K ι : Type*} [CommRing K] (P : MvPolynomial ι K) (i : ι)
    (hP : 0 < P.totalDegree) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hsum : pderiv i P = ∑ m ∈ P.support, pderiv i (monomial m (coeff m P)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [hsum]
  refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ?_
  rw [Finset.sup_lt_iff hP]
  intro m hm
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi, hP]
  · have hm1 : m = (m - Finsupp.single i 1) + Finsupp.single i 1 := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have key : ((m - Finsupp.single i 1).sum fun _ e => e) + 1 = m.sum fun _ e => e := by
      conv_rhs => rw [hm1]
      rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl]
    have hle : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
    show ((m - Finsupp.single i 1).sum fun _ e => e) < _
    omega
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
