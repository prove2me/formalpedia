-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_bilin_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:56.867948+00:00
-- url     : https://prove2.me/submissions/2e4f609c-33e8-425b-940a-4e892dfcc27e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_conj_single_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_sum_coef_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_sum_sum_sum_sum_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
theorem _root_.solution (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) :
    ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v) =
      ∑ a, ∑ b, B (Matrix.single a b 1) (Matrix.single b a 1) := by
  calc ∑ a, ∑ b, B (u * Matrix.single a b 1 * v) (u * Matrix.single b a 1 * v)
      = ∑ a, ∑ b, ∑ c, ∑ d, (u c a * v b d) • B (Matrix.single c d 1) (u * Matrix.single b a 1 * v) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [conj_single_eq u v a b]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, (u c a * v b d) • B (Matrix.single c d 1) (u * Matrix.single b a 1 * v) :=
        sum_sum_sum_sum_comm _
    _ = ∑ c, ∑ d, B (Matrix.single c d 1) (Matrix.single d c 1) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← sum_coef_conj u v huv c d]
        simp only [map_sum, map_smul]
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
