-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wd_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:18.959129+00:00
-- url     : https://prove2.me/submissions/1ffd8180-7570-4df8-a66d-aa51e87d69ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_inner_self

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v) {a b : Fin n} (hab : wdP ε a b) :
    inner ℂ v (E b a (E a b v)) = ((-(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) : ℝ) : ℂ) := by
  rcases hab with ⟨h, he⟩ | ⟨h, he⟩
  · rw [hv.2 a b h he, map_zero, inner_zero_right]
    simp [lt_asymm h]
  · have h1 := hU a b v (E a b v)
    rw [adjSign, if_neg he, wd_inner_self] at h1
    rw [if_pos ⟨h, Ne.symm he⟩]
    push_cast
    linear_combination h1
end ReciprocityTheory.ChartRestriction.DS
