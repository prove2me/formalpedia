-- Prove2me | solution 1 for QuaternionAlgebra.exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e625d910-3f80-50f9-9277-10df20e0cd85

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
import Theorems.Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
import Theorems.Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re imK_zero imJ_zero imI_mul imK_mul imK re_mul re_zero imI_zero imJ imI imJ_mul IsDefiniteRamifiedExactlyAt IsQuadraticDatum isQuadraticDatum_iff forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero"
namespace QuadraticEmbeddingPort
p2m_open "QuaternionAlgebra"

theorem exists_pure_isotropic_of_algEquiv_matrix {K : Type*} [Field K] [CharZero K] (a b : K)
    (φ : ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :
    ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0 := by
  set E : Matrix (Fin 2) (Fin 2) K := Matrix.of ![![0, 1], ![0, 0]] with hE
  have hE0 : E ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [hE] at this
  have hEE : E * E = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hE, Matrix.mul_apply, Fin.sum_univ_two]
  set N : ℍ[K,a,b] := φ.symm E with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hE0
    have : φ N = φ 0 := by rw [h]
    rwa [hN, AlgEquiv.apply_symm_apply, map_zero] at this
  have hNN : N * N = 0 := by rw [hN, ← map_mul, hEE, map_zero]
  have hre := congrArg QuaternionAlgebra.re hNN
  have himI := congrArg QuaternionAlgebra.imI hNN
  have himJ := congrArg QuaternionAlgebra.imJ hNN
  have himK := congrArg QuaternionAlgebra.imK hNN
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero,
    QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero, zero_mul, add_zero] at hre himI himJ himK
  have hre0 : N.re = 0 := by
    by_contra hr
    have hI : N.imI = 0 := by
      have : 2 * N.re * N.imI = 0 := by linear_combination himI
      simpa [hr] using this
    have hJ : N.imJ = 0 := by
      have : 2 * N.re * N.imJ = 0 := by linear_combination himJ
      simpa [hr] using this
    have hK : N.imK = 0 := by
      have : 2 * N.re * N.imK = 0 := by linear_combination himK
      simpa [hr] using this
    rw [hI, hJ, hK] at hre
    have : N.re * N.re = 0 := by linear_combination hre
    exact hr (mul_self_eq_zero.mp this)
  refine ⟨N.imI, N.imJ, N.imK, ?_, ?_⟩
  · rintro ⟨hI, hJ, hK⟩
    exact hN0 (QuaternionAlgebra.ext hre0 hI hJ hK)
  · rw [hre0] at hre
    linear_combination -hre

theorem ternary_isotropic_of_quaternary {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b : K}
    {x₀ x₁ x₂ x₃ : K} (hx : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0))
    (h0 : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
    ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0 := by
  by_cases hY : x₀ ^ 2 - a * x₁ ^ 2 = 0
  ·
    have h23 : -b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 := by linear_combination h0 - hY
    by_cases hx23 : x₂ = 0 ∧ x₃ = 0
    · obtain ⟨rfl, rfl⟩ := hx23
      have hx1 : x₁ ≠ 0 := by
        rintro rfl
        have : x₀ ^ 2 = 0 := by linear_combination hY
        exact hx ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this, rfl, rfl, rfl⟩
      refine ⟨0, x₀ / x₁, 1, ?_, ?_⟩
      · rintro ⟨-, -, h⟩; exact one_ne_zero h
      · have : a = (x₀ / x₁) ^ 2 := by
          field_simp
          linear_combination -hY
        rw [this]; ring
    · refine ⟨0, x₂, x₃, ?_, by linear_combination h23⟩
      rintro ⟨-, h2', h3'⟩
      exact hx23 ⟨h2', h3'⟩
  · refine ⟨2 * (x₀ ^ 2 - a * x₁ ^ 2), -2 * a * (x₀ * x₃ + x₁ * x₂), -2 * (x₀ * x₂ + a * x₁ * x₃), ?_, ?_⟩
    · rintro ⟨h1, -, -⟩
      exact hY ((mul_eq_zero.mp h1).resolve_left h2)
    · linear_combination (-4 * a * (x₀ ^ 2 - a * x₁ ^ 2)) * h0

theorem natGenerator_eq_of_mem (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [hp : Fact p.Prime]
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    simpa using this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp.out).mp hdvd

set_option synthInstance.maxHeartbeats 800000 in

theorem exists_pureNrd_eq_adicCompletion {a b : ℚ} (p : ℕ) [Fact p.Prime]
    (hdef : IsDefiniteRamifiedExactlyAt a b p) (c : ℚ) (hc : ¬ IsSquare ((-c : ℚ) : ℚ_[p]))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x y z : w.adicCompletion ℚ,
      -(algebraMap ℚ (w.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (w.adicCompletion ℚ) a) * (algebraMap ℚ (w.adicCompletion ℚ) b) * z ^ 2
        = algebraMap ℚ (w.adicCompletion ℚ) c := by
  have hp : Fact p.Prime := inferInstance
  have ha : a ≠ 0 := hdef.neg_left.ne
  have hb : b ≠ 0 := hdef.neg_right.ne
  set K := w.adicCompletion ℚ with hK
  set a' : K := algebraMap ℚ K a with ha_def
  set b' : K := algebraMap ℚ K b with hb_def
  set c' : K := algebraMap ℚ K c with hc_def
  have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hua : a' ≠ 0 := by rw [ha_def]; exact (map_ne_zero_iff _ hinj).mpr ha
  have hva : b' ≠ 0 := by rw [hb_def]; exact (map_ne_zero_iff _ hinj).mpr hb
  by_cases hiso : ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a' * x ^ 2 - b' * y ^ 2 + a' * b' * z ^ 2 = 0
  · exact QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero K a' b' hua hva hiso c'
  by_cases hwp : (p : 𝓞 ℚ) ∈ w.asIdeal
  ·
    refine QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
      a b ha hb w ?_ c' ?_
    · rintro ⟨φ⟩
      exact hiso (exists_pure_isotropic_of_algEquiv_matrix a' b' φ)
    ·
      have hℓp := natGenerator_eq_of_mem w p hwp
      haveI hℓprime : Fact (Rat.HeightOneSpectrum.primesEquiv w : ℕ).Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv w).2⟩
      let e := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w).toAlgEquiv
      have ec : e (-c') = ((-c : ℚ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w : ℕ)]) := by
        rw [map_neg, hc_def, e.commutes]
        simp
      rintro ⟨s, hs⟩
      have hsq : IsSquare ((-c : ℚ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv w : ℕ)]) :=
        ⟨e s, by rw [← map_mul, ← hs, ec]⟩
      subst hℓp
      exact hc hsq
  ·
    exfalso
    apply hiso
    have hsplit : ¬ (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x) := fun h =>
      hwp ((hdef.2.2 w).mp h)
    rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hsplit
    push Not at hsplit
    obtain ⟨x₀, x₁, x₂, x₃, h0, hne⟩ := hsplit
    have h0' : x₀ ^ 2 - a' * x₁ ^ 2 - b' * x₂ ^ 2 + a' * b' * x₃ ^ 2 = 0 := by
      rw [ha_def, hb_def]
      simpa using h0
    refine ternary_isotropic_of_quaternary (K := K) two_ne_zero ?_ h0'
    rintro ⟨h₀, h₁, h₂, h₃⟩
    exact hne h₀ h₁ h₂ h₃

theorem exists_pureNrd_eq_real {a : ℚ} (b : ℚ) (ha : a < 0) (c : ℝ) (hc : 0 < c) :
    ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
      + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = c := by
  simp only [eq_ratCast]
  refine ⟨Real.sqrt (c / (-(a : ℝ))), 0, 0, ?_⟩
  have ha'' : (0 : ℝ) < -(a : ℝ) := by exact_mod_cast neg_pos.mpr ha
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne
  rw [Real.sq_sqrt (div_pos hc ha'').le]
  field_simp
  ring

theorem isQuadraticDatum_of_pureNrd_eq {a b : ℚ} (t n : ℤ) (x y z : ℚ)
    (h : -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = (n : ℚ) - (t : ℚ) ^ 2 / 4) :
    IsQuadraticDatum t n (⟨(t : ℚ) / 2, x, y, z⟩ : ℍ[ℚ, a, b]) := by
  rw [isQuadraticDatum_iff]
  ext <;> simp <;> ring_nf
  linear_combination -h

end QuaternionAlgebra.QuadraticEmbeddingPort

open QuaternionAlgebra.QuadraticEmbeddingPort in
theorem solution
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    (t n : ℤ) (hneg : t ^ 2 < 4 * n) (hp : ¬ IsSquare ((t ^ 2 - 4 * n : ℤ) : ℚ_[p])) :
    ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.IsQuadraticDatum t n β := by
  have hpr : Fact p.Prime := inferInstance
  have ha : a ≠ 0 := hdef.neg_left.ne
  have hb : b ≠ 0 := hdef.neg_right.ne

  set c : ℚ := (n : ℚ) - (t : ℚ) ^ 2 / 4 with hc
  have hcpos : 0 < c := by
    have : ((t ^ 2 : ℤ) : ℚ) < ((4 * n : ℤ) : ℚ) := by exact_mod_cast hneg
    push_cast at this
    rw [hc]; linarith
  have hc0 : c ≠ 0 := hcpos.ne'

  have hnsq : ¬ IsSquare ((-c : ℚ) : ℚ_[p]) := by
    rintro ⟨s, hs⟩
    apply hp
    refine ⟨2 * s, ?_⟩
    have h4 : ((t ^ 2 - 4 * n : ℤ) : ℚ_[p]) = 4 * ((-c : ℚ) : ℚ_[p]) := by
      rw [hc]; push_cast; ring
    rw [h4, hs]; ring
  obtain ⟨x, y, z, hxyz⟩ :=
    QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real a b ha hb c hc0
      (exists_pureNrd_eq_adicCompletion p hdef c hnsq)
      (by simpa using exists_pureNrd_eq_real b hdef.neg_left (c : ℝ) (by exact_mod_cast hcpos))
  exact ⟨_, isQuadraticDatum_of_pureNrd_eq t n x y z (by rw [hxyz])⟩

end S_QuaternionAlgebra_exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic
end P2MW
export P2MW.S_QuaternionAlgebra_exists_isQuadraticDatum_of_sq_lt_four_mul_of_not_isSquare_padic (solution)
