-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:22.92563+00:00
-- url     : https://prove2.me/submissions/6fa7cdb2-25c4-448e-88f7-8a6667804516

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB

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
open Matrix NumberField ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end ReciprocityTheory.MultiplicativeHeights
