-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.smith_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:03:55.443338+00:00
-- url     : https://prove2.me/submissions/6844d1d2-1f27-4648-9928-c9d738f00fb7

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_det_Vm
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_mul_Vm
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_VmT_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_piv_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_piv_succ
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_det_blockOne_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_mul_mul_blockOne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_isUnit_det_perm
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
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution (hv : v.Integers R) : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
    ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0
  | 0, n, A => ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
  | d + 1, 0, A => ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
  | d + 1, n + 1, A => by
    classical
    set g : Fin (n + 1) → Fin (d + 1) → R := fun j i => A i j with hg
    obtain ⟨i0, a, u, s, hu, hau, hs, hz, hnz⟩ := exists_pivot hv g
    by_cases ha : a = 0
    · have hA : A = 0 := by
        ext i j
        have := congrFun (hz ha j) i
        simpa [hg] using this
      exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hA]⟩
    · obtain ⟨j0, hj0, hs0⟩ := hnz ha
      have hAj0 : ∀ i, A i j0 = a * u i := fun i => by
        have := congrFun hj0 i
        simpa [hg] using this
      have hAi0 : ∀ l, A i0 l = a * s l := fun l => by
        have := hs l
        simpa [hg] using this
      set B := (Vm i0 u)ᵀ * A * Vm j0 s with hBdef
      have hB : ∀ k l, B k l = if k = i0 then (if l = j0 then a else 0) else
          (if l = j0 then 0 else A k l - s l * (a * u k)) := by
        intro k l
        rw [hBdef, Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
        by_cases hk : k = i0 <;> by_cases hl : l = j0
        · subst hk; subst hl; simp [hAj0, hu]
        · subst hk; simp [hl, hAi0, hs0]; ring
        · subst hl; simp [hk, hAj0, hu, hs0]; ring
        · simp [hk, hl, hAj0, hAi0, hu]; ring
      set A'' : Matrix (Fin d) (Fin n) R := Matrix.of fun l k => B (i0.succAbove l) (j0.succAbove k)
      obtain ⟨P'', Q'', a'', hP'', hQ'', hD''⟩ := solution hv d n A''
      set Cm := B.submatrix (piv i0) (piv j0) with hCm
      have hCeq : ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * B * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Cm := by
        rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
        rfl
      have h0 : ∀ k : Fin n, Cm 0 k.succ = 0 := by
        intro k
        simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, if_true,
          Fin.succAbove_ne, if_false]
      have h1 : ∀ l : Fin d, Cm l.succ 0 = 0 := by
        intro l
        simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, Fin.succAbove_ne, if_false,
          if_true]
      have hsub : (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) = A'' := by
        ext l k
        simp only [hCm, Matrix.of_apply, Matrix.submatrix_apply, piv_succ]
        rfl
      obtain ⟨e00, e0s, es0, ess⟩ := blockOne_mul_mul_blockOne P'' Cm Q'' h0 h1
      refine ⟨bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ,
        Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'', Fin.cons a a'', ?_, ?_, ?_⟩
      · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
        exact hP''.mul (isUnit_det_perm _)
      · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
        exact (isUnit_det_perm _).mul hQ''
      · have hfull : bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ * A *
            (Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'') = bd1 P'' * Cm * bd1 Q'' := by
          rw [← hCeq, hBdef]
          simp only [Matrix.mul_assoc]
        intro j k
        rw [hfull]
        refine Fin.cases ?_ (fun l => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
        · rw [e00]
          simp [hCm, piv_zero, hB]
        · rw [e0s]
          simp
        · rw [es0]
          simp
        · rw [ess, hsub, hD'']
          simp [Fin.val_succ]
end ReciprocityTheory.PGsh.Up.Smith
