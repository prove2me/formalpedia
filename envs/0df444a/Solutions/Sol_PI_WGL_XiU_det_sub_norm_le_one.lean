-- Prove2me | solution 1 for PI.WGL.XiU.det_sub_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:15.253803+00:00
-- url     : https://prove2.me/submissions/89887098-5afa-4e6b-9d2a-dc4b11e14ae8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Theorems.Thm_PI_WGL_XiU_sub_contract
import Theorems.Thm_PI_WGL_XiU_multiset_prod_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix
namespace PI.WGL.XiU
theorem _root_.solution {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) :
    ‖(Matrix.of fun p q => x (I p) (J q)).det‖ ≤ 1 := by
  set A := Matrix.of fun p q => x (I p) (J q) with hA
  rw [Matrix.det_eq_prod_roots_charpoly]
  apply multiset_prod_norm_le_one
  intro μ hμ
  have hroot : A.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).1 hμ
  have hspec : μ ∈ spectrum ℂ A := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hspec
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hspec
  have hAv : A *ᵥ v = μ • v := by
    first
    | rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hv
    | rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  have hc := sub_contract x hx I J hI hJ v
  rw [← hA, hAv] at hc
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum] at hc
  have hpos : 0 < ∑ q, Complex.normSq (v q) := by
    obtain ⟨q, hq⟩ := Function.ne_iff.1 hv0
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hq)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (v i)) (Finset.mem_univ q))
  have h1 : Complex.normSq μ ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have h2 := Complex.normSq_eq_norm_sq μ
  nlinarith [norm_nonneg μ]
end PI.WGL.XiU
