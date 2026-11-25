-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.unitary_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:49.176683+00:00
-- url     : https://prove2.me/submissions/149fc0e0-1510-457a-a8c3-bf1f7bc87e20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
private lemma stdH_apply_lemma (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (z w : m → ℂ) :
    UnitDetRootDefs.stdH L m z w = ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp only [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h
end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)}
    (hiso : UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) :
    LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1 := by
  have hA0 : ((UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, UnitDetRootDefs.area, abs_ne_zero]
    change (conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d)).im ≠ 0
    have e : conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d) =
        ((Complex.normSq lam * a : ℝ) : ℂ) * UnitDetRootDefs.cmTheta b d := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [e, Complex.im_ofReal_mul]
    have hθ : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by
      simp [UnitDetRootDefs.cmTheta]
    rw [hθ]
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact (mul_pos (mul_pos h1 h2) (by positivity)).ne'
  have hU : (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).transpose *
      (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).map (starRingEnd ℂ) = 1 := by
    ext k l
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
    have h := hiso (Pi.single k 1) (Pi.single l 1)
    rw [stdH_apply_lemma, stdH_apply_lemma] at h
    rw [mul_left_cancel₀ (inv_ne_zero hA0) h]
    rw [Finset.sum_eq_single k (fun i _ hik => by rw [Pi.single_eq_of_ne hik, zero_mul])
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same, one_mul, Pi.single_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hd' := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd'
  rw [← LinearMap.det_toMatrix', RingHom.map_det, RingHom.mapMatrix_apply]
  exact hd'
end PI.UnitaryGroupMassFormula.UnitDetRoot
