-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:45.839131+00:00
-- url     : https://prove2.me/submissions/3e1a78dd-4a52-4dfa-a3f3-0264b3696420

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) : wVal r m g i = g i := by
  unfold wVal
  rw [if_neg h]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
