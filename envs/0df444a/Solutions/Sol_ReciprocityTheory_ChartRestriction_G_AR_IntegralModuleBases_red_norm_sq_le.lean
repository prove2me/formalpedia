-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.red_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:47.814625+00:00
-- url     : https://prove2.me/submissions/6738bf68-8d1c-4815-b8a1-9f16ad61cb04

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_norm_sq_le_pow_gs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_gs_sq_ge
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_det_gram_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (m D : ℝ) (hm0 : 0 < m)
    (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (hD : (Matrix.gram ℝ b).det ≤ D) (i : Fin d) :
    ‖b i‖ ^ 2 ≤ 2 ^ (d * (d - 1)) * D / m ^ (d - 1) := by
  have hb := hr.1
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = m / 2 ^ (d - 1) := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  have hG : ∀ j, L ≤ ‖gs b j‖ ^ 2 := fun j => by rw [hL]; exact gs_sq_ge b hr m hm j
  have hprod : L ^ (d - 1) ≤ ∏ j ∈ univ.erase i, ‖gs b j‖ ^ 2 := by
    have := Finset.prod_le_prod (s := univ.erase i) (f := fun _ => L) (g := fun j => ‖gs b j‖ ^ 2)
      (fun _ _ => hLpos.le) (fun j _ => hG j)
    rw [Finset.prod_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
      Fintype.card_fin] at this
    exact this
  have hdet : ‖gs b i‖ ^ 2 * ∏ j ∈ univ.erase i, ‖gs b j‖ ^ 2 ≤ D := by
    rw [Finset.mul_prod_erase univ (fun j => ‖gs b j‖ ^ 2) (mem_univ i), ← det_gram_eq b hb]
    exact hD
  have hGi : ‖gs b i‖ ^ 2 * L ^ (d - 1) ≤ D :=
    le_trans (mul_le_mul_of_nonneg_left hprod (sq_nonneg _)) hdet
  have hLp : 0 < L ^ (d - 1) := pow_pos hLpos _
  have hGi' : ‖gs b i‖ ^ 2 ≤ D / L ^ (d - 1) := by rw [le_div_iff₀ hLp]; exact hGi
  have hid : (2:ℝ) ^ i.val ≤ 2 ^ (d - 1) :=
    pow_le_pow_right₀ (by norm_num) (by have := i.isLt; omega)
  have key : D / L ^ (d - 1) = 2 ^ ((d - 1) * (d - 1)) * D / m ^ (d - 1) := by
    rw [hL, div_pow, ← pow_mul, div_div_eq_mul_div]; ring
  have hnat : d * (d - 1) = (d - 1) + (d - 1) * (d - 1) := by
    cases d with
    | zero => rfl
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have hexp : (2:ℝ) ^ (d * (d - 1)) = 2 ^ (d - 1) * 2 ^ ((d - 1) * (d - 1)) := by
    rw [← pow_add, hnat]
  have hDL : 0 ≤ D / L ^ (d - 1) := le_trans (sq_nonneg _) hGi'
  calc ‖b i‖ ^ 2 ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := norm_sq_le_pow_gs b hr i
    _ ≤ 2 ^ (d - 1) * (D / L ^ (d - 1)) := mul_le_mul hid hGi' (sq_nonneg _) (by positivity)
    _ = 2 ^ (d * (d - 1)) * D / m ^ (d - 1) := by rw [key, hexp]; ring
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
