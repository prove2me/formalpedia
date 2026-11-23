-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.countable_mvPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:48.400626+00:00
-- url     : https://prove2.me/submissions/0fd5adc7-04d0-4e9d-9c81-e2ecb1881cca

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
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution {σ R : Type*} [Countable σ] [CommSemiring R] [Countable R] :
    Countable (MvPolynomial σ R) := by
  classical
  refine Function.Surjective.countable (f := fun f : (σ →₀ ℕ) →₀ R => f.sum fun m a => monomial m a) ?_
  intro p
  refine ⟨Finsupp.onFinset p.support (fun m => coeff m p) (fun m hm => mem_support_iff.2 hm), ?_⟩
  dsimp only
  rw [Finsupp.onFinset_sum _ (fun m => by simp)]
  exact (MvPolynomial.as_sum p).symm
end ReciprocityTheory.ChartRestriction.G.T0.NPB
