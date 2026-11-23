-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.waExt_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:21.310823+00:00
-- url     : https://prove2.me/submissions/1d7352a9-6863-44b3-80c1-e3dedcea492a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB

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
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by
  rw [waExt, Fin.cons_succ, Fin.snoc_castSucc]
end ReciprocityTheory.MultiplicativeHeights
