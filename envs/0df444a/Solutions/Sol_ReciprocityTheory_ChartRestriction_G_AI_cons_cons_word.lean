-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.cons_cons_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:34.940421+00:00
-- url     : https://prove2.me/submissions/3d3cda38-d6c1-4171-8ea4-e65747eae121

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {VW : Type*} (D k i : ℕ) (hk : 1 ≤ k) (x x₁ x₂ a : VW) :
    (Fin.cons x (Fin.cons x (word D k i x₁ x₂ a)) : Fin (D + 2) → VW) =
      fun j : Fin (D + 2) => consWord k i x x₁ x₂ a j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [consWord]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [consWord]
    · simp only [Fin.cons_succ, consWord, word, Fin.val_succ]
      split_ifs <;> first | rfl | omega
end ReciprocityTheory.ChartRestriction.G.AI
