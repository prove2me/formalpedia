-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:08.147703+00:00
-- url     : https://prove2.me/submissions/256fb435-a012-4632-b5a1-48f43ec4d08b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (j j' : ι) :
    Hf (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single j' 1) = if j = j' then 1 else 0 := by
  simp only [Hf, EuclideanSpace.single_apply]
  by_cases h : j = j'
  · subst h
    simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i = j
    · subst h1
      simp [h]
    · simp [h1]
end ReciprocityTheory.ChartRestriction.G.I2
