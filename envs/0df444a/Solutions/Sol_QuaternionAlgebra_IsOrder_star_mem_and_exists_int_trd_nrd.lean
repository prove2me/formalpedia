-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.star_mem_and_exists_int_trd_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/566cdb6e-1b27-5b2e-aea4-3071300dddf3

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra
open Polynomial

namespace PoleStarInt

variable {a b : ℚ}

def subalg (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) : Subalgebra ℤ ℍ[ℚ, a, b] where
  carrier := Λ
  mul_mem' hx hy := hΛ.mul_mem hx hy
  one_mem' := hΛ.one_mem
  add_mem' hx hy := Λ.add_mem hx hy
  zero_mem' := Λ.zero_mem
  algebraMap_mem' z := by
    have : (algebraMap ℤ ℍ[ℚ, a, b] z) = z • (1 : ℍ[ℚ, a, b]) := by simp
    rw [this]
    exact Λ.smul_mem z hΛ.one_mem

theorem isIntegral_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) : IsIntegral ℤ x := by
  have hS : (subalg Λ hΛ).toSubmodule = Λ := by
    ext y; rfl
  exact IsIntegral.of_mem_of_fg (subalg Λ hΛ) (by rw [hS]; exact hΛ.fg) x hx

theorem quad_rel (x : ℍ[ℚ, a, b]) :
    x * x - (trd x) • x + (nrd x) • (1 : ℍ[ℚ, a, b]) = 0 := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [trd, nrd, QuaternionAlgebra.mk_mul_mk] <;> ring

noncomputable def redPoly (x : ℍ[ℚ, a, b]) : ℚ[X] := X ^ 2 - C (trd x) * X + C (nrd x)

theorem degree_lt_two (x : ℍ[ℚ, a, b]) : (C (trd x) * X : ℚ[X]).degree < (X ^ 2 : ℚ[X]).degree := by
  rw [degree_X_pow]
  exact lt_of_le_of_lt (degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)

theorem redPoly_monic (x : ℍ[ℚ, a, b]) : (redPoly x).Monic := by
  unfold redPoly
  have h1 := degree_lt_two x
  have hm1 : (X ^ 2 - C (trd x) * X : ℚ[X]).Monic := (monic_X_pow 2).sub_of_left h1
  have hdeg : (X ^ 2 - C (trd x) * X : ℚ[X]).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt h1, degree_X_pow]; rfl
  exact hm1.add_of_left (by rw [hdeg]; exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.two_pos))

theorem redPoly_coeff_one (x : ℍ[ℚ, a, b]) : (redPoly x).coeff 1 = - trd x := by
  simp [redPoly, coeff_X_pow, coeff_C]

theorem redPoly_coeff_zero (x : ℍ[ℚ, a, b]) : (redPoly x).coeff 0 = nrd x := by
  simp [redPoly, coeff_X_pow, coeff_C]

theorem aeval_redPoly (x : ℍ[ℚ, a, b]) : aeval x (redPoly x) = 0 := by
  simp only [redPoly, map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X]
  have := quad_rel x
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, pow_two]
  exact this

theorem trd_coe (r : ℚ) : trd ((r : ℚ) : ℍ[ℚ, a, b]) = 2 * r := by
  simp [trd]

theorem exists_int_trd_nrd {x : ℍ[ℚ, a, b]} (hint : IsIntegral ℤ x) :
    ∃ t n : ℤ, trd x = (t : ℚ) ∧ nrd x = (n : ℚ) := by
  obtain ⟨p, hp, hpx⟩ := hint
  have hpx' : aeval x p = 0 := hpx
  set pQ : ℚ[X] := p.map (algebraMap ℤ ℚ) with hpQ
  have hpQx : aeval x pQ = 0 := by rw [hpQ, aeval_map_algebraMap]; exact hpx'
  have hfm := redPoly_monic x
  set r : ℚ[X] := pQ %ₘ redPoly x with hr
  have hdiv : r + redPoly x * (pQ /ₘ redPoly x) = pQ := modByMonic_add_div pQ (redPoly x)
  have hrx : aeval x r = 0 := by
    have := congr_arg (aeval x) hdiv
    rw [map_add, map_mul, aeval_redPoly, zero_mul, add_zero, hpQx] at this
    exact this
  have hrdeg : r.degree ≤ 1 := by
    have h2 : (redPoly x).degree = 2 := by
      unfold redPoly; compute_degree!
    have := degree_modByMonic_lt pQ hfm
    rw [h2] at this
    exact Order.le_of_lt_succ (by exact_mod_cast this)
  have hr_eq : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_degree_le_one hrdeg
  have hrx' : (r.coeff 1) • x + (r.coeff 0) • (1 : ℍ[ℚ, a, b]) = 0 := by
    rw [hr_eq] at hrx
    simp only [map_add, map_mul, aeval_C, aeval_X] at hrx
    rwa [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at hrx
  by_cases h1 : r.coeff 1 = 0
  ·
    have h0 : r.coeff 0 = 0 := by
      rw [h1, zero_smul, zero_add, ← Algebra.algebraMap_eq_smul_one] at hrx'
      exact (algebraMap ℚ ℍ[ℚ, a, b]).injective (by rw [map_zero]; exact hrx')
    have hr0 : r = 0 := by rw [hr_eq, h1, h0]; simp
    have hdvd : redPoly x ∣ pQ := (modByMonic_eq_zero_iff_dvd hfm).mp hr0
    obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hp hdvd
    rw [hfm.leadingCoeff, C_1, mul_one] at hg'
    refine ⟨-(g'.coeff 1), g'.coeff 0, ?_, ?_⟩
    · have := congr_arg (fun q : ℚ[X] => q.coeff 1) hg'
      simp only [coeff_map, redPoly_coeff_one, eq_intCast] at this
      push_cast
      linarith
    · have := congr_arg (fun q : ℚ[X] => q.coeff 0) hg'
      simp only [coeff_map, redPoly_coeff_zero, eq_intCast] at this
      exact this.symm
  ·
    set c : ℚ := -(r.coeff 0) / (r.coeff 1) with hc
    have hxc : x = ((c : ℚ) : ℍ[ℚ, a, b]) := by
      have : x = (r.coeff 1)⁻¹ • (-( (r.coeff 0) • (1 : ℍ[ℚ, a, b]))) := by
        rw [← eq_neg_iff_add_eq_zero] at hrx'
        rw [← hrx', smul_smul, inv_mul_cancel₀ h1, one_smul]
      rw [this, hc]
      ext <;> simp <;> ring
    have hcint : IsIntegral ℤ c := by
      have : IsIntegral ℤ (algebraMap ℚ ℍ[ℚ, a, b] c) := by
        rw [show algebraMap ℚ ℍ[ℚ, a, b] c = ((c : ℚ) : ℍ[ℚ, a, b]) from rfl, ← hxc]
        exact ⟨p, hp, hpx⟩
      exact (isIntegral_algebraMap_iff (QuaternionAlgebra.coe_injective)).mp this
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
    have hm' : (m : ℚ) = c := by simpa using hm
    refine ⟨2 * m, m * m, ?_, ?_⟩
    · rw [hxc, trd_coe, ← hm']; push_cast; ring
    · rw [hxc, nrd_coe, ← hm']; push_cast; ring

end PoleStarInt

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    star x ∈ Λ ∧ ∃ t n : ℤ, trd x = (t : ℚ) ∧ nrd x = (n : ℚ) := by
  have key : ∃ t n : ℤ, trd x = (t : ℚ) ∧ nrd x = (n : ℚ) :=
    PoleStarInt.exists_int_trd_nrd (PoleStarInt.isIntegral_of_mem hΛ hx)
  refine ⟨?_, key⟩
  obtain ⟨t, n, ht, hn⟩ := key
  have hstar : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by
    rw [← add_star_eq_coe_trd]; abel
  rw [hstar, ht]
  refine Λ.sub_mem ?_ hx
  have : (((t : ℤ) : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, Algebra.smul_def, mul_one]; rfl
  rw [this]
  exact Λ.smul_mem t hΛ.one_mem

end S_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd (solution)
