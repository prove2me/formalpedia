-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.nc_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:59.464303+00:00
-- url     : https://prove2.me/submissions/97b56715-9ce7-46a8-822e-74ada2b8bd7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}
private lemma mul_apply_eq_ite_of_lower_block_scalar {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : NC k r a) (c : ℂ)
    {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
      x i j = if i = j then c else 0) :
    ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
      (x * a) i j = if i = j then c else 0 := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [ha j j hj (min_le_left _ _), if_pos rfl, mul_one]
    exact hx i j hj hi
  · intro l _ hlj
    by_cases hl : min j.val r ≤ l.val
    · rw [ha l j hj hl, if_neg hlj, mul_zero]
    · push_neg at hl
      have hlr : l.val < r := lt_of_lt_of_le hl (min_le_right _ _)
      have h := hx i l (by omega) (by rw [min_eq_left hlr.le]; omega)
      rw [h, if_neg (by intro h'; rw [h'] at hi; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h
end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) (ha : NC k r a) : NC k r a⁻¹ := by
  have hfix := mul_apply_eq_ite_of_lower_block_scalar (k := k) (r := r) (a := a) ha
  let V : Submodule ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    { carrier := {x | ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val →
          x i j = if i = j then x 0 0 else 0}
      add_mem' := by
        intro x y hx hy i j hj hi
        simp only [Set.mem_setOf_eq] at hx hy
        rw [Matrix.add_apply, hx i j hj hi, hy i j hj hi, Matrix.add_apply]
        split_ifs <;> simp
      zero_mem' := by
        intro i j _ _
        simp
      smul_mem' := by
        intro c x hx i j hj hi
        simp only [Set.mem_setOf_eq] at hx
        rw [Matrix.smul_apply, hx i j hj hi, Matrix.smul_apply]
        split_ifs <;> simp }
  have hV : ∀ x ∈ V, LinearMap.mulRight ℂ a x ∈ V := by
    intro x hx i j hj hi
    have h00 : (x * a) 0 0 = x 0 0 := by
      rw [hfix (x 0 0) hx 0 0 (by simp) (by simp), if_pos rfl]
    show (x * a) i j = if i = j then (x * a) 0 0 else 0
    rw [h00]
    exact hfix (x 0 0) hx i j hj hi
  let f : V →ₗ[ℂ] V := (LinearMap.mulRight ℂ a).restrict hV
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a = y * a := congrArg Subtype.val hxy
    have h2 := congrArg (· * a⁻¹) h1
    simp only [Matrix.mul_assoc, mul_inv_UH hU, Matrix.mul_one] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have h1V : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ V := by
    intro i j _ _
    simp [Matrix.one_apply]
  obtain ⟨x, hx⟩ := hsurj ⟨1, h1V⟩
  have hxa : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * a = 1 := congrArg Subtype.val hx
  have hxinv : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = a⁻¹ := by
    calc (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = x * (a * a⁻¹) := by rw [mul_inv_UH hU, Matrix.mul_one]
      _ = (x * a) * a⁻¹ := by rw [Matrix.mul_assoc]
      _ = a⁻¹ := by rw [hxa, Matrix.one_mul]
  have hc : (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) 0 0 = 1 := by
    have h := hfix ((x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) 0 0) x.2 0 0 (by simp) (by simp)
    rw [hxa, if_pos rfl, Matrix.one_apply_eq] at h
    exact h.symm
  intro i j hj hi
  rw [← hxinv]
  have h := x.2 i j hj hi
  rw [hc] at h
  exact h
end PI.QuotSetU.UnitaryGroupMassFormula.SW
