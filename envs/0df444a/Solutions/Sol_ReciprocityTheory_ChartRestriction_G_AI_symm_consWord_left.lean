-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.symm_consWord_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:21.814611+00:00
-- url     : https://prove2.me/submissions/9d59a592-24df-4dfd-9099-3f94a434a80f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_swap_nat

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin (D + 2) => V) ℝ) (hI : IsSymmForm I) (k i : ℕ) (hi : i < k)
    (hD : 2 * k ≤ D + 1) (x₁ x₂ a : V) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  refine (symm_swap_nat I hI (consWord k i x₁ x₁ x₂ a) 0 2 (by omega) (by omega)).trans ?_
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega
end ReciprocityTheory.ChartRestriction.G.AI
