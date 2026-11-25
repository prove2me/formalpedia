-- Prove2me | solution 1 for PI.IsoDetW.Loc.chi_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:37.99701+00:00
-- url     : https://prove2.me/submissions/5e1b650e-c912-440f-9ecc-414c628411d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
import Theorems.Thm_PI_IsoDetW_Loc_chi_one
import Theorems.Thm_PI_IsoDetW_Loc_chi_mul
import Theorems.Thm_PI_IsoDetW_Loc_chi_transvection_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (c : K) :
    chi R P (Matrix.transvection i j c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, Matrix.transvection_zero, chi_one]
  set D : Matrix ι ι K := Matrix.diagonal (Function.update 1 i c)
  set D' : Matrix ι ι K := Matrix.diagonal (Function.update 1 i c⁻¹)
  have hDD' : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    by_cases ha : a = i
    · subst ha; simp [hc]
    · simp [Function.update_of_ne ha]
  have hdet : ∀ M N : Matrix ι ι K, M * N = 1 → M.det ≠ 0 := fun M N h hM => by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, hM, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hD : D.det ≠ 0 := hdet D D' hDD'
  have hD'D : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    by_cases ha : a = i
    · subst ha; simp [hc]
    · simp [Function.update_of_ne ha]
  have hD' : D'.det ≠ 0 := hdet D' D hD'D
  have ht1 : (Matrix.transvection i j (1 : K)).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero
  have he : Matrix.transvection i j c = D * Matrix.transvection i j 1 * D' := by
    ext a b
    simp only [D, D', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    rcases eq_or_ne a i with rfl | ha
    · rcases eq_or_ne b a with rfl | hba
      · simp [Function.update_self, hij.symm]
        field_simp
      · rcases eq_or_ne b j with rfl | hbj
        · simp [Function.update_self, Function.update_of_ne hba, hba.symm]
        · simp [hba.symm, hbj.symm]
    · rcases eq_or_ne a b with rfl | hab
      · simp [Function.update_of_ne ha, ha.symm]
      · simp [hab, ha.symm, Function.update_of_ne ha]
  have h1 := chi_transvection_int (K := K) P hij 1
  rw [map_one] at h1
  rw [he, chi_mul P (by rw [Matrix.det_mul]; exact mul_ne_zero hD ht1) hD', chi_mul P hD ht1, h1,
    add_zero, ← chi_mul P hD hD', hDD', chi_one]
end PI.IsoDetW.Loc
