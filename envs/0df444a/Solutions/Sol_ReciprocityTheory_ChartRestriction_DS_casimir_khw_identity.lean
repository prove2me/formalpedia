-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_khw_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:04.57218+00:00
-- url     : https://prove2.me/submissions/a9ce3295-bc21-4a02-ad55-6b794fedf6d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_signedOrder_irrefl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_signedOrder_iff_not_swap_of_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_offdiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_nsq_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_inner_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_term
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_split


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
    {c : ℝ} (hc : casimir E v = (c : ℂ) • v) :
    c * ‖v‖ ^ 2 = (nsq (μ + rhoC ε - rhoN ε) - nsq (rhoC ε - rhoN ε)) * ‖v‖ ^ 2 -
      2 * ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), ‖E b a v‖ ^ 2 := by
  have hs := casimir_split hE (wdP ε) (signedOrder_irrefl ε) (signedOrder_iff_not_swap_of_ne ε)
  have h1 : inner ℂ v (casimir E v) = ((c * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hc, inner_smul_right, wd_inner_self]; push_cast; ring
  have hA : ∀ a, inner ℂ v (E a a (E a a v)) = (((μ a) ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [hv.1 a, map_smul, hv.1 a, inner_smul_right, inner_smul_right, wd_inner_self]
    push_cast; ring
  have hB : ∀ a b, wdP ε a b → inner ℂ v ((E a a - E b b + 2 • (E b a * E a b)) v) =
      (((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) : ℝ) : ℂ) := by
    intro a b hab
    rw [two_smul, LinearMap.add_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      inner_add_right, inner_add_right, inner_sub_right, hv.1 a, hv.1 b, inner_smul_right,
      inner_smul_right, wd_inner_self, wd_term ε hU hv hab]
    push_cast; ring
  have h2 : inner ℂ v (casimir E v) = ((∑ a, (μ a) ^ 2 * ‖v‖ ^ 2 +
      ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
        ((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0)) : ℝ) : ℂ) := by
    rw [hs, LinearMap.add_apply, inner_add_right]
    simp only [LinearMap.sum_apply, inner_sum]
    push_cast
    congr 1
    · exact sum_congr rfl (fun a _ => by rw [Module.End.mul_apply, hA]; push_cast; ring)
    · refine sum_congr rfl (fun a _ => ?_)
      refine sum_congr rfl (fun b hb => ?_)
      rw [hB a b (mem_filter.1 hb).2]; push_cast; ring
  have h4 : c * ‖v‖ ^ 2 = ∑ a, (μ a) ^ 2 * ‖v‖ ^ 2 +
      ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
        ((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0)) := by
    exact_mod_cast h1.symm.trans h2
  have e1 : ∑ a, (μ a) ^ 2 * ‖v‖ ^ 2 = nsq μ * ‖v‖ ^ 2 := by
    rw [nsq, dot, sum_mul]; exact sum_congr rfl (fun _ _ => by ring)
  have e2 : ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
        ((μ a - μ b) * ‖v‖ ^ 2 + 2 * -(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0)) =
      (∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b)) * ‖v‖ ^ 2 -
        2 * ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b),
          (if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) := by
    rw [sum_mul, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun a _ => ?_)
    rw [sum_mul, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun b _ => by ring)
  rw [h4, e1, e2, wd_diag, wd_offdiag ε (fun a b => ‖E a b v‖ ^ 2), nsq_shift]
  ring
end ReciprocityTheory.ChartRestriction.DS
