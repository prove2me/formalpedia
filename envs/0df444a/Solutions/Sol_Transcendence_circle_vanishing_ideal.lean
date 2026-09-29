-- Prove2me | solution 1 for Transcendence.circle_vanishing_ideal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:22.728418+00:00
-- url     : https://prove2.me/submissions/5321761f-c9fb-4556-836d-5bfa595d80a6

import Mathlib

namespace S7W1_circle_vanishing_ideal

open Polynomial

variable {K : Subfield ℂ}

/-- `K[X₀, X₁] ≃ₐ[K] K[X][X]`: `X₀` becomes the outer variable, `X₁` the inner one. -/
noncomputable def e : MvPolynomial (Fin 2) K ≃ₐ[K] K[X][X] :=
  (MvPolynomial.finSuccEquiv K 1).trans (mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

/-- Evaluation of `K[X][X]` at `y` (inner variable) and `x` (outer variable). -/
noncomputable def ev (x y : ℂ) : K[X][X] →ₐ[K] ℂ :=
  eval₂AlgHom (aeval y) x fun _ => .all _ _

@[simp] lemma e_X_zero : e (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = X := by
  simp [e, MvPolynomial.finSuccEquiv_X_zero]

@[simp] lemma e_X_one : e (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) = C X := by
  have h : MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) = C (MvPolynomial.X 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  simp [e, h]

@[simp] lemma e_C (a : K) : e (MvPolynomial.C a : MvPolynomial (Fin 2) K) = C (C a) :=
  (e (K := K)).commutes a

@[simp] lemma ev_X (x y : ℂ) : ev x y (X : K[X][X]) = x := by simp [ev]

@[simp] lemma ev_C (x y : ℂ) (p : K[X]) : ev x y (C p) = aeval y p := by simp [ev]

lemma ev_e (x y : ℂ) (P : MvPolynomial (Fin 2) K) :
    ev x y (e P) = MvPolynomial.aeval ![x, y] P := by
  suffices (ev x y).comp (e (K := K)).toAlgHom = MvPolynomial.aeval ![x, y] from
    DFunLike.congr_fun this P
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp

/-- Forward direction: the circle divides every polynomial vanishing at `(x, y)`. -/
theorem dvd_of_aeval_eq_zero {x y : ℂ} {ρ : K} (hρ : ρ ≠ 0) (hxy : x ^ 2 + y ^ 2 = (ρ : ℂ))
    (hy : Transcendental K y) {P : MvPolynomial (Fin 2) K}
    (hP : MvPolynomial.aeval ![x, y] P = 0) :
    (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - MvPolynomial.C ρ) ∣ P := by
  have hxy' : x ^ 2 + y ^ 2 = algebraMap K ℂ ρ := hxy
  set D : K[X][X] := X ^ 2 + C (X ^ 2 - C ρ) with hDdef
  have hD : e (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - MvPolynomial.C ρ) = D := by
    rw [map_sub, map_add, map_pow, map_pow, e_X_zero, e_X_one, e_C, hDdef, C_sub, C_pow]
    ring
  have hmon : D.Monic := monic_X_pow_add_C _ two_ne_zero
  have hD2 : D.natDegree = 2 := natDegree_X_pow_add_C
  rw [← map_dvd_iff e, hD, ← modByMonic_eq_zero_iff_dvd hmon]
  have hev : ev x y (e P %ₘ D) = 0 := by
    rw [modByMonic_eq_sub_mul_div, map_sub (ev x y), map_mul (ev x y), ← hD, ev_e, ev_e, hP]
    simp [hxy']
  have hr1 : (e P %ₘ D).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt (e P) hmon (fun h => by simp [h] at hD2)
    omega
  generalize e P %ₘ D = r at hev hr1 ⊢
  rw [eq_X_add_C_of_natDegree_le_one hr1] at hev ⊢
  generalize r.coeff 1 = A at hev ⊢
  generalize r.coeff 0 = B at hev ⊢
  have hlin : aeval y A * x + aeval y B = 0 := by simpa using hev
  -- Squaring and using `x² = ρ − y²`: `A² (ρ − T²) = B²` at `T = y`, hence in `K[T]`.
  have key : A ^ 2 * (C ρ - X ^ 2) = B ^ 2 := by
    rw [← sub_eq_zero]
    refine (injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp hy) _ ?_
    simp only [map_sub, map_mul, map_pow, aeval_C, aeval_X]
    linear_combination (aeval y A * x - aeval y B) * hlin - aeval y A ^ 2 * hxy'
  -- `X² − ρ` is separable, hence squarefree, and not a unit: so `A = 0`, then `B = 0`.
  have hA : A = 0 := by
    by_contra hA
    obtain ⟨M, rfl⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp
      ⟨_, key.symm⟩
    have hM : X ^ 2 - C ρ = -(M * M) := by
      have := mul_left_cancel₀ (pow_ne_zero 2 hA)
        (key.trans (by ring) : A ^ 2 * (C ρ - X ^ 2) = A ^ 2 * (M * M))
      linear_combination -this
    have hu := (separable_X_pow_sub_C (n := 2) ρ (by norm_num) hρ).squarefree M
      ⟨-1, by rw [hM]; ring⟩
    have hunit : IsUnit (X ^ 2 - C ρ : K[X]) := hM ▸ (hu.mul hu).neg
    have := natDegree_eq_zero_of_isUnit hunit
    rw [natDegree_X_pow_sub_C] at this
    omega
  have hB : B = 0 := by simpa [hA] using key.symm
  simp [hA, hB]

end S7W1_circle_vanishing_ideal

-- Forward: `dvd_of_aeval_eq_zero`. Backward: the circle itself vanishes at `(x, y)`.
open S7W1_circle_vanishing_ideal in
theorem solution {K : Subfield ℂ} {x y : ℂ} {ρ : K} (hρ : ρ ≠ 0)
    (hxy : x ^ 2 + y ^ 2 = (ρ : ℂ)) (hy : Transcendental K y) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.aeval ![x, y] P = 0 ↔
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - MvPolynomial.C ρ) ∣ P := by
  refine ⟨dvd_of_aeval_eq_zero hρ hxy hy, fun ⟨Q, hQ⟩ => ?_⟩
  simp [hQ, hxy, show algebraMap K ℂ ρ = ρ from rfl]

#print axioms solution
