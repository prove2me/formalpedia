-- Prove2me | solution 1 for QuaternionAlgebra.involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/13f2fb07-d153-57f5-b790-d7c8e6a05db7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul

set_option autoImplicit false

p2m_open "QuaternionAlgebra P2MW.S_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul.QuaternionAlgebra"
open scoped Quaternion

universe u v

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "star_smul re imI_mul imJ_smul re_smul imI_one imK_mul re_one imK imK_smul imJ_one re_mul imI_smul imK_one imJ imI imJ_mul star_eq_neg"
namespace TwistedConjSol
p2m_open "QuaternionAlgebra"

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem re_eq_zero_of_mul_self {a b : R} (t : ℍ[R, a, b]) {c : R} (hc : 0 < c)
    (ht2 : t * t = (-c) • (1 : ℍ[R, a, b])) : t.re = 0 := by
  by_contra hre
  have h1 := congrArg QuaternionAlgebra.re ht2
  have h2 := congrArg QuaternionAlgebra.imI ht2
  have h3 := congrArg QuaternionAlgebra.imJ ht2
  have h4 := congrArg QuaternionAlgebra.imK ht2
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
    QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one,
    zero_mul, mul_zero, add_zero, smul_eq_mul, mul_one] at h1 h2 h3 h4
  have hI : t.imI = 0 := by
    have : 2 * t.re * t.imI = 0 := by linear_combination h2
    simpa [hre] using this
  have hJ : t.imJ = 0 := by
    have : 2 * t.re * t.imJ = 0 := by linear_combination h3
    simpa [hre] using this
  have hK : t.imK = 0 := by
    have : 2 * t.re * t.imK = 0 := by linear_combination h4
    simpa [hre] using this
  rw [hI, hJ, hK] at h1
  nlinarith [mul_self_nonneg t.re]

theorem star_eq_neg_of_mul_self {a b : R} (t : ℍ[R, a, b]) {c : R} (hc : 0 < c)
    (ht2 : t * t = (-c) • (1 : ℍ[R, a, b])) : star t = -t :=
  QuaternionAlgebra.star_eq_neg.mpr (re_eq_zero_of_mul_self t hc ht2)

end QuaternionAlgebra.TwistedConjSol

open QuaternionAlgebra.TwistedConjSol in
theorem solution
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {a b c : R} (hc : 0 < c)
    (t : ℍ[R, a, b]) (ht : t * t = (-c) • (1 : ℍ[R, a, b]))
    {I : Type v} (e : I → ℍ[R, a, b]) (he : Function.Injective e)
    (σ : I → I) (hσ : ∀ d : I, t * e (σ d) = star (e d) * t) :
    Function.Involutive σ := by
  have hc0 : (c : R) ≠ 0 := hc.ne'

  set u : ℍ[R, a, b] := -((c⁻¹ : R) • t) with hu
  have htu : t * u = 1 := by
    rw [hu, mul_neg, mul_smul_comm, ht, smul_smul, mul_neg, inv_mul_cancel₀ hc0, neg_smul, neg_neg, one_smul]
  have hut : u * t = 1 := by
    rw [hu, neg_mul, smul_mul_assoc, ht, smul_smul, mul_neg, inv_mul_cancel₀ hc0, neg_smul, neg_neg, one_smul]
  have hstar_t : star t = -t := star_eq_neg_of_mul_self t hc ht
  have hstar_u : star u = -u := by
    rw [hu, star_neg, QuaternionAlgebra.star_smul, hstar_t, smul_neg]

  have hform : ∀ d : I, e (σ d) = u * star (e d) * t := by
    intro d
    have := congrArg (u * ·) (hσ d)
    simpa [← mul_assoc, hut] using this
  intro d
  apply he
  rw [hform, hform, star_mul, star_mul, hstar_u, hstar_t, star_star]
  have : u * (-t * (e d * -u)) * t = (u * t) * e d * (u * t) := by noncomm_ring
  rw [this, hut, one_mul, mul_one]

end S_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul
end P2MW
export P2MW.S_QuaternionAlgebra_involutive_of_mul_self_eq_neg_smul_of_forall_mul_eq_star_mul (solution)
