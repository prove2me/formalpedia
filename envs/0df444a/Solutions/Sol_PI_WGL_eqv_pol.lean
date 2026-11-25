-- Prove2me | solution 1 for PI.WGL.eqv_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:27.365312+00:00
-- url     : https://prove2.me/submissions/8a815447-b139-457a-a008-9ec842e31bc9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
import Theorems.Thm_PI_WGL_lmapPoly_coeff
import Theorems.Thm_PI_WGL_lmapPoly_eval
import Theorems.Thm_PI_WGL_det_one_add_single
import Theorems.Thm_PI_WGL_embGL_transvec
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_pol_eq_rowDiv
import Theorems.Thm_PI_WGL_rowGen_coeff_zero
import Theorems.Thm_PI_WHw_coeff_mem_of_eval
import Theorems.Thm_PI_WHw_det_one_add_single_ne
import Theorems.Thm_PI_WHw_eval_rowGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (a b : Fin n) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    φ (pol ℂ a b s) + (if a = b then (mu.detShift : ℂ) • φ s else 0) =
      pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) (φ s) +
        (if a = b then (lam.detShift : ℂ) • φ s else 0) := by
  subst h
  have hι : ∀ x : Fin n, Fin.castLE (by omega : n ≤ n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  rw [hι a, hι b]
  set d1 := mu.detShift with hd1
  set d2 := lam.detShift with hd2
  set K : ℤ := |d1| + |d2| with hK
  have hK1 : 0 ≤ d1 + K := by have := neg_abs_le d1; have := abs_nonneg d2; omega
  have hK2 : 0 ≤ d2 + K := by have := neg_abs_le d2; have := abs_nonneg d1; omega
  set e1 := (d1 + K).toNat with he1d
  set e2 := (d2 + K).toNat with he2d
  have he1 : (e1 : ℤ) = d1 + K := Int.toNat_of_nonneg hK1
  have he2 : (e2 : ℤ) = d2 + K := Int.toNat_of_nonneg hK2
  set Q : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :=
    if a = b then Polynomial.X + 1 else 1 with hQ
  set P := Q ^ e1 * lmapPoly φ (rowGen ℂ a b s) - Q ^ e2 * rowGen ℂ a.castSucc b.castSucc (φ s) with hP
  have key : ∀ t : ℕ, P.eval (C (t : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro t
    rw [Submodule.mem_bot]
    set D : ℂ := if a = b then (t : ℂ) + 1 else 1 with hD
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (PI.WHw.det_one_add_single_ne a b t)
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (t : ℂ) := rfl
    have hgT : (g : Matrix (Fin n) (Fin n) ℂ).transpose = 1 + Matrix.single b a (t : ℂ) := by
      rw [hgv, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have hgT' := embGL_transvec g a b t hgv
    have hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, det_one_add_single]
    have hu' : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hgT', det_one_add_single]
      rcases eq_or_ne a b with hab | hab
      · subst hab; simp [hD]
      · simp [hD, hab, Ne.symm hab]
    have huu : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g :=
      Units.ext (hu'.trans hu.symm)
    have heq := hφ.2 g s hs
    unfold sqAct detPow at heq
    rw [hgT, hgT', huu, map_smul, ← PI.WHw.eval_rowGen, ← PI.WHw.eval_rowGen] at heq
    set u := Matrix.GeneralLinearGroup.det g
    have heq2 := congrArg (fun x => ((u ^ K : ℂˣ) : ℂ) • x) heq
    simp only [smul_smul, ← Units.val_mul, ← zpow_add] at heq2
    rw [show K + mu.detShift = (e1 : ℤ) by omega, show K + lam.detShift = (e2 : ℤ) by omega,
      zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu] at heq2
    have hQe : Q.eval (C (t : ℂ)) = C D := by
      rw [hQ, hD]; split_ifs <;> simp
    rw [hP, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, hQe, lmapPoly_eval, ← C_pow, ← C_pow, ← smul_eq_C_mul, ← smul_eq_C_mul, heq2, sub_self]
  have h1 := PI.WHw.coeff_mem_of_eval ⊥ P key 1
  rw [Submodule.mem_bot] at h1
  have hL0 : (lmapPoly φ (rowGen ℂ a b s)).coeff 0 = φ s := by
    rw [lmapPoly_coeff, rowGen_coeff_zero]
  have hL1 : (lmapPoly φ (rowGen ℂ a b s)).coeff 1 = φ (pol ℂ a b s) := by
    rw [lmapPoly_coeff, pol_eq_rowDiv]; rfl
  have hG0 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 0 = φ s := rowGen_coeff_zero ℂ _ _ _
  have hG1 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 1 = pol ℂ a.castSucc b.castSucc (φ s) := by
    rw [pol_eq_rowDiv]; rfl
  have hc1 : ∀ (e : ℕ) (F : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)),
      (Q ^ e * F).coeff 1 = F.coeff 1 + (if a = b then (e : MvPolynomial _ ℂ) * F.coeff 0 else 0) := by
    intro e F
    rw [hQ]
    split_ifs with hab
    · rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_add_one_pow]
      simp
    · simp
  rw [hP, Polynomial.coeff_sub, hc1, hc1, hL0, hL1, hG0, hG1] at h1
  by_cases hab : a = b
  · simp only [hab, if_true] at h1 ⊢
    have c1 : ((e1 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d1 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he1
    have c2 : ((e2 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d2 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he2
    rw [c1, c2, map_add, map_add] at h1
    rw [smul_eq_C_mul, smul_eq_C_mul]
    subst hab
    linear_combination h1
  · simp only [hab, if_false, add_zero] at h1 ⊢
    exact sub_eq_zero.mp h1
end PI.WGL
