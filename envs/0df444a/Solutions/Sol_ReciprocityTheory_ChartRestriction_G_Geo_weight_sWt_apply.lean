-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.weight_sWt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:34.527927+00:00
-- url     : https://prove2.me/submissions/71b35e64-cc66-42fd-92d0-178786c30a25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF

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
theorem _root_.solution {r : ℕ} (n : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ) (k : K) :
    Finsupp.weight (sWt k0 r) n k =
      (∑ j, n (Sum.inl j)) + (if h : k = k0 then 0 else n (Sum.inr ⟨k, h⟩)) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply,
    Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [sWt, oneK]
  · by_cases h : k = k0
    · subst h
      rw [dif_pos rfl]
      refine Finset.sum_eq_zero fun k' _ => ?_
      simp [sWt, Finsupp.single_apply, k'.2]
    · rw [dif_neg h, Finset.sum_eq_single ⟨k, h⟩]
      · simp [sWt]
      · intro k' _ hk'
        have : k'.1 ≠ k := fun e => hk' (Subtype.ext e)
        simp [sWt, Finsupp.single_apply, this]
      · simp
end ReciprocityTheory.ChartRestriction.G.Geo
