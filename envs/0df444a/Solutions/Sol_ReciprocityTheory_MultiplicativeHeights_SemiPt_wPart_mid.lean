-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wPart_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:28.302802+00:00
-- url     : https://prove2.me/submissions/3d9665bb-c326-4df2-97ae-1103f376e315

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
theorem _root_.solution (r m : ℕ) (i : Fin r) (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) :
    wPart r m i = i := by
  unfold wPart
  rw [if_neg h]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
