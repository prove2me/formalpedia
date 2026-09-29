-- Prove2me | solution 1 for Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8173de9a-257b-53ca-bf41-cb8b74b26d93

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BLRFaceB

open Polynomial

variable {k : Type} [Field k]

theorem trace_mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) k) :
    Matrix.trace (A * A) = Matrix.trace A ^ 2 - 2 * A.det := by
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem poly_identity (t d t₂ : k) :
    (C (t ^ 2 - 2 * d - t₂) * X ^ 2 : k[X]) =
      (X ^ 4 - C t₂ * X ^ 2 + C (d ^ 2)) - (X ^ 2 - C t * X + C d) * (X ^ 2 + C t * X + C d) := by
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

variable {W : Type} [AddCommGroup W] [Module k W]

theorem smul_sq_eq_zero (x : Module.End k W) (t d t₂ : k)
    (h1 : x ^ 2 - t • x + d • (1 : Module.End k W) = 0)
    (h2 : (x ^ 2) ^ 2 - t₂ • x ^ 2 + (d ^ 2) • (1 : Module.End k W) = 0) :
    (t ^ 2 - 2 * d - t₂) • x ^ 2 = 0 := by
  have e1 : aeval x (X ^ 2 - C t * X + C d : k[X]) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    exact h1
  have e2 : aeval x (X ^ 4 - C t₂ * X ^ 2 + C (d ^ 2) : k[X]) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, _root_.smul_pow, one_pow]
    have : x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this]
    exact h2
  have e3 : aeval x (C (t ^ 2 - 2 * d - t₂) * X ^ 2 : k[X]) = (t ^ 2 - 2 * d - t₂) • x ^ 2 := by
    simp only [map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [← e3, poly_identity, map_sub, map_mul, e1, e2, zero_mul, sub_zero]

theorem trace_mul_self_of_finrank_two {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) (f : Module.End k V) :
    LinearMap.trace k V (f * f) = LinearMap.trace k V f ^ 2 - 2 * LinearMap.det f := by
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_mul,
    ← LinearMap.det_toMatrix b, trace_mul_self_fin_two]

end BLRFaceB

theorem solution
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V)
    {M : Type} [AddCommGroup M] [Module k M] [Nontrivial M]
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∀ g : G, LinearMap.det (ρV g) = d g := by
  intro g
  set x := ρM g with hx
  set t := LinearMap.trace k V (ρV g) with ht
  set dd : k := ((d g : kˣ) : k) with hdd
  have h1 : x ^ 2 - t • x + dd • (1 : Module.End k M) = 0 := by rw [sq]; exact hrel g
  have hgg : ρM (g * g) = x ^ 2 := by rw [map_mul, sq]
  have hdgg : ((d (g * g) : kˣ) : k) = dd ^ 2 := by rw [map_mul, Units.val_mul, sq]
  have h2' := hrel (g * g)
  rw [hgg, hdgg, ← sq] at h2'
  have hs := BLRFaceB.smul_sq_eq_zero x t dd (LinearMap.trace k V (ρV (g * g))) h1 h2'

  have hx2 : x ^ 2 ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := exists_ne (0 : M)
    apply hw
    have hinv : ρM g⁻¹ * ρM g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have : (ρM g⁻¹ * ρM g⁻¹ * (x ^ 2)) w = w := by
      rw [sq, hx, ← mul_assoc, mul_assoc (ρM g⁻¹), hinv, mul_one, hinv, Module.End.one_apply]
    rw [← this, h0, mul_zero, LinearMap.zero_apply]
  have hscalar : t ^ 2 - 2 * dd - LinearMap.trace k V (ρV (g * g)) = 0 := by
    rcases smul_eq_zero.mp hs with h | h
    · exact h
    · exact absurd h hx2
  rw [map_mul, BLRFaceB.trace_mul_self_of_finrank_two hV] at hscalar
  have : (2 : k) * dd = 2 * LinearMap.det (ρV g) := by linear_combination -hscalar
  exact (mul_left_cancel₀ h2 this).symm

end S_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
end P2MW
export P2MW.S_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero (solution)
