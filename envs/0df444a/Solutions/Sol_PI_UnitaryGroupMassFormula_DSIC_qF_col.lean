-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.qF_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:52:42.432801+00:00
-- url     : https://prove2.me/submissions/f64e2fd4-0ecd-4dc5-b745-6ad8e16e1475

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_ofFn_prod_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_ofFn_prod_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_intCast_mul_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_sum_fun_eq_sum_perm
import Theorems.Thm_Formalism_REAL_qSkewCol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R) (hE : Formalism.REAL.GlRel E)
    (B : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) :
    qF (fun x a b => ∑ d, B d b • Formalism.REAL.Tm E x a d) u = B.det • Formalism.REAL.qdet E u := by
  classical
  have hperm : ∀ π : Equiv.Perm (Fin n), Formalism.REAL.qminor E id (π : Fin n → Fin n) u =
      ((Equiv.Perm.sign π : ℤ) : R) * Formalism.REAL.qdet E u :=
    fun π => Formalism.REAL.qSkewCol R n n E hE id id π u
  have hzero : ∀ d : Fin n → Fin n, ¬ Function.Injective d → Formalism.REAL.qminor E id d u = 0 := by
    intro d hd
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hd
    have hsw : d ∘ (Equiv.swap i j) = d := by
      funext k
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hij]
      · rw [h2, hij]
      · rfl
    have h := Formalism.REAL.qSkewCol R n n E hE id d (Equiv.swap i j) u
    rw [hsw, Equiv.Perm.sign_swap hne] at h
    have h2 : (2 : ℂ) • Formalism.REAL.qminor E id d u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      simp
    calc Formalism.REAL.qminor E id d u = (1 / 2 : ℂ) • ((2 : ℂ) • Formalism.REAL.qminor E id d u) := by
          rw [smul_smul]; norm_num
      _ = 0 := by rw [h2, smul_zero]
  unfold qF
  simp_rw [ofFn_prod_sum, ofFn_prod_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  have hq : ∀ d : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (σ k) (d k)).prod) = Formalism.REAL.qminor E id d u :=
    fun d => rfl
  simp_rw [hq]
  rw [sum_fun_eq_sum_perm (fun d => (∏ k, B (d k) k) • Formalism.REAL.qminor E id d u)
    (fun d hd => by rw [hzero d hd, smul_zero])]
  simp_rw [hperm, intCast_mul_eq, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, mul_comm]
end PI.UnitaryGroupMassFormula.DSIC
