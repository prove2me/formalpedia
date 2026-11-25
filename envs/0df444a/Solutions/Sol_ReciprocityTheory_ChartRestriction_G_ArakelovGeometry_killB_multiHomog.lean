-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.killB_multiHomog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:50.341081+00:00
-- url     : https://prove2.me/submissions/55eec3b9-11b8-48f8-9c98-93207522b945

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_killB_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (T : Finset K) {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) :
    killB T s = 0 ∨ killB T s = s := by
  classical
  by_cases hT : ∃ k ∈ T, c k ≠ 0
  · left
    obtain ⟨k, hkT, hck⟩ := hT
    rw [s.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    have h := hs m hm k
    rw [← h] at hck
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hck
    rw [killB_monomial, if_pos ⟨⟨k, i⟩, hkT, hi⟩]
  · right
    push_neg at hT
    have key : ∀ m ∈ s.support, killB T (monomial m (coeff m s)) = monomial m (coeff m s) := by
      intro m hm
      rw [killB_monomial, if_neg]
      rintro ⟨p, hpT, hp⟩
      have h := hs m hm p.1
      rw [hT p.1 hpT] at h
      exact hp ((Finset.sum_eq_zero_iff.mp h) p.2 (Finset.mem_univ _))
    calc killB T s = killB T (∑ m ∈ s.support, monomial m (coeff m s)) := by rw [← s.as_sum]
      _ = ∑ m ∈ s.support, killB T (monomial m (coeff m s)) := map_sum _ _ _
      _ = ∑ m ∈ s.support, monomial m (coeff m s) := Finset.sum_congr rfl key
      _ = s := s.as_sum.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
