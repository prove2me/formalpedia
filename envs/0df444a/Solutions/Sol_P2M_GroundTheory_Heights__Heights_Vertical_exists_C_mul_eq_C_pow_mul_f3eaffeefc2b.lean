-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_exists_C_mul_eq_C_pow_mul_f3eaffeefc2b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:48.213839+00:00
-- url     : https://prove2.me/submissions/9d9fa438-9e74-43c8-8842-670d02436ffd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by
  have hlt : v.intValuation a < 1 := by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := (v.intValuation_lt_one_iff_dvd a).mp hlt
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hle
    have h2 : v.asIdeal ^ 2 ∣ Ideal.span {a} := ⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩
    have h3 := (v.intValuation_le_pow_iff_dvd a 2).mpr h2
    rw [ha, exp_le_exp] at h3
    norm_num at h3
  have hJj : ¬ J ^ j ≤ v.asIdeal := fun h => hJv (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJj
  have hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j} := by
    rw [← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]
  have hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)} := by
    have h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) *
        Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp
    rw [← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨t, htv, h, by rw [← hh, mul_comm]⟩
end GroundTheory.Heights₂.Heights.Vertical
