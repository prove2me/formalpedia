-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hasDerivAt_mul_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:35.621664+00:00
-- url     : https://prove2.me/submissions/68e7532a-17aa-4a88-8b22-6403ccea7f2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : ℝ → A} {a b : A}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    HasDerivAt (fun t => f t * g t) (a + b) 0 := by
  have h := hf.mul hg
  rw [hf0, hg0, one_mul, mul_one] at h
  exact h
end ReciprocityTheory.ChartRestriction.DS.HW
