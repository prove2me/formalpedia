-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_khw_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:39.382738+00:00
-- url     : https://prove2.me/submissions/63dc21d4-b8c2-44ae-935f-c4c408a2838b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_khw_identity

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
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v)
    (hv0 : v ≠ 0) {c : ℝ} (hc : casimir E v = (c : ℂ) • v) :
    c + nsq (rhoC ε - rhoN ε) ≤ nsq (μ + rhoC ε - rhoN ε) := by
  have h := casimir_khw_identity ε hE hU hv hc
  have hS : 0 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), ‖E b a v‖ ^ 2 :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  have hpos : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  apply le_of_mul_le_mul_right _ hpos
  linarith
end ReciprocityTheory.ChartRestriction.DS
