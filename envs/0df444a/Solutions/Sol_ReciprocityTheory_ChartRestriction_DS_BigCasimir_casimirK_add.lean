-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.casimirK_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:31.287647+00:00
-- url     : https://prove2.me/submissions/3edacdcf-5c10-4e26-b014-5af9bbdfb6f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_sum_compact_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution (A B : Fin n → Fin n → Module.End ℂ X)
    (hAB : ∀ a b c d, A a b * B c d = B c d * A a b) :
    casimirK ε (A + B) = casimirK ε A + casimirK ε B +
      2 • ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), B a b * A b a := by
  unfold casimirK
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), A a b * B b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), B a b * A b a := by
    rw [sum_compact_swap]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hAB b a a b
  rw [this, two_nsmul]
  abel
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
