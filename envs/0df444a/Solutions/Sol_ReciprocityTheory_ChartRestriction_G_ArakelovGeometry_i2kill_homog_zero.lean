-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2kill_homog_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:57.779188+00:00
-- url     : https://prove2.me/submissions/941b392b-0586-449b-b85b-58871b0411f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime

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
theorem _root_.solution {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) {k : K}
    (hk : a k = 0) : i2kill k s = s := by
  conv_rhs => rw [← aeval_X_left_apply s]
  rw [i2kill, aeval_def, aeval_def]
  apply eval₂_congr
  intro v m hv hm
  by_cases h : v.1 = k
  · exfalso
    have hsum := hs m (mem_support_iff.2 hm) k
    rw [hk, Finset.sum_eq_zero_iff] at hsum
    obtain ⟨k', i⟩ := v
    simp only at h
    subst h
    exact (Finsupp.mem_support_iff.1 hv) (hsum i (Finset.mem_univ _))
  · simp [h]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
