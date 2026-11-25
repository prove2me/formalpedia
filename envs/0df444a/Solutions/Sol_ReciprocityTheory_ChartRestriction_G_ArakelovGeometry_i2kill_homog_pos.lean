-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2kill_homog_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:39.688995+00:00
-- url     : https://prove2.me/submissions/0f8a0688-9578-4cfb-ab5b-73abb901d024

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
    (hk : a k ≠ 0) : i2kill k s = 0 := by
  rw [i2kill, aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hsum := hs m hm k
  obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    exact hk (by rw [← hsum]; exact Finset.sum_eq_zero fun i _ => hne i)
  rw [Finset.prod_eq_zero (i := ⟨k, i⟩) (Finsupp.mem_support_iff.2 hi) (by simp [zero_pow hi]),
    mul_zero]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
