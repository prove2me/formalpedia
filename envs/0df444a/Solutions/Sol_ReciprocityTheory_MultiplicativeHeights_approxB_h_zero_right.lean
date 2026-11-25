-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:19.686137+00:00
-- url     : https://prove2.me/submissions/b9751dd1-130b-43e4-a6cc-9719c97325c2

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
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h]
end ReciprocityTheory.MultiplicativeHeights
