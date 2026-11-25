-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.blockOne_mul_mul_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:01.118005+00:00
-- url     : https://prove2.me/submissions/6b216a12-637c-4d65-8e09-584a593ed796

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution {d n : ℕ} (P : Matrix (Fin d) (Fin d) R) (Cm : Matrix (Fin (d + 1)) (Fin (n + 1)) R)
    (Q : Matrix (Fin n) (Fin n) R) (h0 : ∀ k : Fin n, Cm 0 k.succ = 0)
    (h1 : ∀ l : Fin d, Cm l.succ 0 = 0) :
    (bd1 P * Cm * bd1 Q) 0 0 = Cm 0 0 ∧ (∀ k : Fin n, (bd1 P * Cm * bd1 Q) 0 k.succ = 0) ∧
      (∀ l : Fin d, (bd1 P * Cm * bd1 Q) l.succ 0 = 0) ∧
      ∀ (l : Fin d) (k : Fin n), (bd1 P * Cm * bd1 Q) l.succ k.succ =
        (P * (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) * Q) l k := by
  have hPC0 : ∀ j : Fin (n + 1), (bd1 P * Cm) 0 j = Cm 0 j := by
    intro j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPCs : ∀ (l : Fin d) (j : Fin (n + 1)), (bd1 P * Cm) l.succ j = ∑ m, P l m * Cm m.succ j := by
    intro l j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨?_, fun k => ?_, fun l => ?_, fun l k => ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hPCs, h1]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [hPCs, blockOne_zero_succ_alt, mul_zero, zero_add, blockOne_succ_succ_alt, Matrix.mul_apply, Matrix.of_apply]
end ReciprocityTheory.PGsh.Up.Smith
