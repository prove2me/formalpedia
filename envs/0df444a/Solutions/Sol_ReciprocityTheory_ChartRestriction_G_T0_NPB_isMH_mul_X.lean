-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.isMH_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:36.526058+00:00
-- url     : https://prove2.me/submissions/53a8dfd5-c02c-42fd-a1df-acf27229f84b

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {R : Type*} [CommSemiring R] {B n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (a + Pi.single i 1) (f * X (i, j)) := by
  classical
  intro s hs b
  rw [support_mul_X, Finset.mem_map] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  simp only [addRightEmbedding_apply, Finsupp.add_apply, Finset.sum_add_distrib, hf s' hs' b,
    Pi.add_apply]
  congr 1
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [hb]
end ReciprocityTheory.ChartRestriction.G.T0.NPB
