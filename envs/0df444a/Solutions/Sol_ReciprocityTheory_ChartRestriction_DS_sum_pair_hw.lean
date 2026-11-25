-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sum_pair_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:57.610219+00:00
-- url     : https://prove2.me/submissions/d398a986-2553-4497-994e-6958d7f4f9f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_pair_apply_hw

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (S : Fin n → Fin n → Prop) [DecidableRel S] (hS : ∀ a b, S a b → S b a)
    (hd : ∀ a, E a a v = (μ a : ℂ) • v) (hv : ∀ a b, a < b → S a b → E a b v = 0) :
    (∑ a, ∑ b ∈ univ.filter (fun b => S a b), E a b * E b a) v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b : ℝ) : ℂ) • v := by
  simp only [LinearMap.sum_apply, Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : S a b := (Finset.mem_filter.1 hb).2
  exact pair_apply_hw hE hd (fun h => hv a b h hab) (fun h => hv b a h (hS a b hab))
end ReciprocityTheory.ChartRestriction.DS
