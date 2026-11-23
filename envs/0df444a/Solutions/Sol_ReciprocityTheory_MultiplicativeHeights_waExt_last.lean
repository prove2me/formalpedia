-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.waExt_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:20.709365+00:00
-- url     : https://prove2.me/submissions/d51eaa4a-643d-4bd1-8cd6-7a08ac043f84

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
theorem _root_.solution {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f (Fin.last (n + 1)) = y := by
  rw [waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
end ReciprocityTheory.MultiplicativeHeights
