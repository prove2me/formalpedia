-- Prove2me | solution 1 for ReciprocityTheory.PGsh.charTable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:17.588796+00:00
-- url     : https://prove2.me/submissions/f7db87ac-cc9f-4d6c-a5b2-b5854a619ca9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.PGsh
open Matrix
section
variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
private lemma invPerm_apply (e : G ≃ AddChar G K) (h : G) :
    invPerm e h = e.symm (e h)⁻¹ := rfl
private lemma transpose_mul_self (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g)ᵀ * (Matrix.of fun g h : G => e h g) =
      (Fintype.card G : K) • (invPerm e).permMatrix K := by
  ext g h
  have key : ∀ x, e g x * e h x = (e g * e h) x := fun x => (AddChar.mul_apply _ _ _).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, smul_eq_mul, key]
  by_cases hgh : e g * e h = 1
  · have h1 : invPerm e g = h := by
      rw [invPerm_apply, inv_eq_of_mul_eq_one_right hgh, Equiv.symm_apply_apply]
    rw [if_pos h1, hgh]
    simp
  · have h1 : ¬ invPerm e g = h := by
      intro h1
      apply hgh
      rw [invPerm_apply] at h1
      rw [← h1, Equiv.apply_symm_apply, mul_inv_cancel]
    rw [if_neg h1, AddChar.sum_eq_zero_of_ne_one hgh, mul_zero]
private lemma det_sq (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g).det ^ 2 =
      (Fintype.card G : K) ^ Fintype.card G * (Equiv.Perm.sign (invPerm e) : K) := by
  have h := congrArg Matrix.det (transpose_mul_self e)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_permutation] at h
  rw [sq]
  exact h
end
end ReciprocityTheory.PGsh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
namespace ReciprocityTheory.PGsh
theorem _root_.solution : CharTableStatement := by
  intro K _ G _ _ _ e
  rw [det_sq e]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (invPerm e)) with h | h <;> rw [h]
  · left; simp
  · right; simp
end ReciprocityTheory.PGsh
