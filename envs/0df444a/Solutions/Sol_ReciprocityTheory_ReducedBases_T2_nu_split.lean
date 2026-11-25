-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.nu_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:33.98138+00:00
-- url     : https://prove2.me/submissions/e54e4c46-c19f-43a8-a246-29c2c78f639d

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
private lemma mu_self_of_linearIndependent (b : Fin d → E) (hb : LinearIndependent ℝ b) (j : Fin d) :
    mu b j j = 1 := by
  have e : ⟪gs b j, b j⟫_ℝ = ‖gs b j‖ ^ 2 := by
    conv_lhs => rw [gramSchmidt_def'' ℝ b j]
    rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (ne_of_gt (Finset.mem_Iio.mp hi)), mul_zero]
  have hne : gs b j ≠ 0 := by
    first
    | exact gramSchmidt_ne_zero j hb
    | exact gramSchmidt_ne_zero (𝕜 := ℝ) j hb
  rw [mu, e]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
private lemma nu_eq_add_sum_mu (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    nu b c j = c j + ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j := by
  unfold nu
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun l : Fin d => j.val + 1 ≤ l.val), add_comm]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [mu_self_of_linearIndependent b hb j, mul_one]
  · intro l hl hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hl
    have h1 : l.val ≠ j.val := fun h => hlj (Fin.ext h)
    have hlt : l < j := Fin.lt_iff_val_lt_val.mpr (by omega)
    have h0 : ⟪gs b j, b l⟫_ℝ = 0 := by
      first
      | exact gramSchmidt_inv_triangular ℝ b hlt
      | exact gramSchmidt_inv_triangular b hlt
    simp [mu, h0]
  · intro hj
    exfalso
    apply hj
    simp
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    nu b c j = c j + ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j := by
  exact nu_eq_add_sum_mu b hb c j
end ReciprocityTheory.ReducedBases.T2
