-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.scaledTorusMean_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:50.314441+00:00
-- url     : https://prove2.me/submissions/a8492e73-211c-4d84-a666-22c8f647132c

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) :
    scaledTorusMean (fun _ => 1) f = torusMean f := by
  unfold scaledTorusMean torusMean
  simp only [one_mul]
end ReciprocityTheory.MultiplicativeHeights
