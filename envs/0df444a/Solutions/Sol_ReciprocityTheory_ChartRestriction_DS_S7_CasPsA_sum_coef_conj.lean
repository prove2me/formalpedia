-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.sum_coef_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:18.96635+00:00
-- url     : https://prove2.me/submissions/9be36ab3-fe15-4e27-8f44-e4dd7a80265f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_entry_conj_single

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
theorem _root_.solution (u v : Matrix (Fin n) (Fin n) ℂ) (huv : u * v = 1) (c d : Fin n) :
    ∑ a, ∑ b, (u c a * v b d) • (u * Matrix.single b a (1 : ℂ) * v) = Matrix.single d c (1 : ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, entry_conj_single]
  have h1 : ∀ x y, ∑ k, u x k * v k y = (1 : Matrix (Fin n) (Fin n) ℂ) x y := fun x y => by
    rw [← huv, Matrix.mul_apply]
  calc ∑ a, ∑ b, u c a * v b d * (u i b * v a j)
      = (∑ a, u c a * v a j) * (∑ b, u i b * v b d) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = Matrix.single d c (1 : ℂ) i j := by
        rw [h1, h1, Matrix.one_apply, Matrix.one_apply, Matrix.single_apply]
        split_ifs <;> simp_all
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
