-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_cons_single_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:37.212344+00:00
-- url     : https://prove2.me/submissions/409f5126-0299-4cb6-9263-7285ae2ab3ab

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (Matrix.single 0 0 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (1 / ((n : ℂ) + 1)) * mdisc (fun k => (B k).submatrix Fin.succ Fin.succ) := by
  set A : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Fin.cons (Matrix.single 0 0 1) B with hA
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm,
    ← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := n)).symm, Fintype.sum_prod_type,
    Finset.sum_eq_single (0 : Fin (n + 1))]
  · have hterm : ∀ τ : Equiv.Perm (Fin n),
        (Matrix.of fun i j => A (Equiv.Perm.decomposeFin.symm (0, τ) j) i j).det =
          (Matrix.of fun i j => (B (τ j)).submatrix Fin.succ Fin.succ i j).det := by
      intro τ
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · simp only [Matrix.of_apply, Equiv.Perm.decomposeFin_symm_apply_zero, hA, Fin.cons_zero,
          Matrix.single_apply, and_self, if_true, Fin.val_zero, pow_zero, one_mul]
        congr 1
      · intro b _ hb
        simp [hA, Equiv.Perm.decomposeFin_symm_apply_zero, Ne.symm hb]
      · simp
    simp_rw [hterm]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp
  · intro p _ hp
    refine Finset.sum_eq_zero fun τ _ => ?_
    set σ := Equiv.Perm.decomposeFin.symm (p, τ) with hσ
    have hσ0 : σ 0 = p := Equiv.Perm.decomposeFin_symm_apply_zero p τ
    have hj : σ.symm 0 ≠ 0 := by
      intro h
      apply hp
      have := σ.apply_symm_apply 0
      rw [h, hσ0] at this
      exact this
    apply Matrix.det_eq_zero_of_column_eq_zero (σ.symm 0)
    intro i
    simp [hA, Ne.symm hj]
  · simp
end ReciprocityTheory.AnForm.A
