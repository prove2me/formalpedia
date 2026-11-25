-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wd_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:50.527777+00:00
-- url     : https://prove2.me/submissions/c21e3196-8313-40ae-b6dc-6bfec98085ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (if b < a ∧ ε b ≠ ε a then f a b else 0) =
      ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), f b a := by
  have h2 : ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then f b a else 0) =
      ∑ a, ∑ b, (if b < a ∧ ε b ≠ ε a then f a b else 0) := Finset.sum_comm
  simp only [sum_filter]
  rw [h2]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  by_cases h : b < a ∧ ε b ≠ ε a
  · have hp : wdP ε a b := Or.inr ⟨h.1, Ne.symm h.2⟩
    simp [h, hp]
  · simp [h]
end ReciprocityTheory.ChartRestriction.DS
