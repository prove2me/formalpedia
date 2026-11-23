-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_outer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:28.834216+00:00
-- url     : https://prove2.me/submissions/055e63c0-e531-4d07-a520-3ae295c9b88b

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
    (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) : wVal r m g i = 1 := by
  unfold wVal
  rw [if_pos h]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
