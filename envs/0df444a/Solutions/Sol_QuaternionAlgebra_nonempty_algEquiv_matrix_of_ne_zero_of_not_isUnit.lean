-- Prove2me | solution 1 for QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/95f91ec4-74fe-54d7-873f-7b4f734fc8fd

import Mathlib
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit

set_option autoImplicit false

open scoped Quaternion

namespace C8NSplit

variable {F : Type*} [Field F] {a b : F}

def N (x : ℍ[F, a, b]) : F := x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def bar (x : ℍ[F, a, b]) : ℍ[F, a, b] := ⟨x.re, -x.imI, -x.imJ, -x.imK⟩

theorem mul_bar (x : ℍ[F, a, b]) : x * bar x = algebraMap F ℍ[F, a, b] (N x) := by
  ext <;> simp [bar, N, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem bar_mul (x : ℍ[F, a, b]) : bar x * x = algebraMap F ℍ[F, a, b] (N x) := by
  ext <;> simp [bar, N, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem N_eq_zero_of_not_isUnit {x : ℍ[F, a, b]} (hxu : ¬ IsUnit x) : N x = 0 := by
  by_contra hN
  apply hxu
  refine ⟨⟨x, (N x)⁻¹ • bar x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, mul_bar, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hN, one_smul]
  · rw [smul_mul_assoc, bar_mul, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem exists_norm_eq [NeZero (2 : F)] (ha : a ≠ 0) (x : ℍ[F, a, b]) (hx : x ≠ 0) (hN : N x = 0) :
    ∃ u v : F, b = u * u - a * (v * v) := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have key : x.re ^ 2 - a * x.imI ^ 2 = b * (x.imJ ^ 2 - a * x.imK ^ 2) := by
    unfold N at hN; linear_combination hN
  by_cases hs : x.imJ ^ 2 - a * x.imK ^ 2 = 0
  ·
    have hsq : ∃ c : F, c ≠ 0 ∧ a = c ^ 2 := by
      by_cases hK : x.imK = 0
      · have hJ : x.imJ = 0 := by
          rw [hK] at hs; simpa using hs
        have h0 : x.re ^ 2 - a * x.imI ^ 2 = 0 := by rw [key, hs, mul_zero]
        by_cases hI : x.imI = 0
        · exfalso
          have hR : x.re = 0 := by rw [hI] at h0; simpa using h0
          exact hx (QuaternionAlgebra.ext hR hI hJ hK)
        · refine ⟨x.re / x.imI, ?_, ?_⟩
          · intro hc
            rw [div_eq_zero_iff] at hc
            rcases hc with hc | hc
            · rw [hc] at h0
              have : a * x.imI ^ 2 = 0 := by simpa using h0
              rcases mul_eq_zero.1 this with h | h
              · exact ha h
              · exact hI (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)
            · exact hI hc
          · rw [div_pow, eq_div_iff (pow_ne_zero 2 hI)]
            linear_combination (-1 : F) * h0
      · refine ⟨x.imJ / x.imK, ?_, ?_⟩
        · intro hc
          rw [div_eq_zero_iff] at hc
          rcases hc with hc | hc
          · rw [hc] at hs
            have : a * x.imK ^ 2 = 0 := by simpa using hs
            rcases mul_eq_zero.1 this with h | h
            · exact ha h
            · exact hK (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)
          · exact hK hc
        · rw [div_pow, eq_div_iff (pow_ne_zero 2 hK)]
          linear_combination (-1 : F) * hs
    obtain ⟨c, hc, hac⟩ := hsq
    refine ⟨(b + 1) / 2, (b - 1) / (2 * c), ?_⟩
    rw [hac]
    field_simp
    ring
  · refine ⟨(x.re * x.imJ - a * x.imI * x.imK) / (x.imJ ^ 2 - a * x.imK ^ 2),
      (x.imI * x.imJ - x.re * x.imK) / (x.imJ ^ 2 - a * x.imK ^ 2), ?_⟩
    have mult : (x.re * x.imJ - a * x.imI * x.imK) ^ 2 - a * (x.imI * x.imJ - x.re * x.imK) ^ 2
        = (x.re ^ 2 - a * x.imI ^ 2) * (x.imJ ^ 2 - a * x.imK ^ 2) := by ring
    field_simp
    linear_combination (-1 : F) * mult - (x.imJ ^ 2 - a * x.imK ^ 2) * key

theorem main [NeZero (2 : F)] (ha : a ≠ 0) (hb : b ≠ 0)
    (x : ℍ[F, a, b]) (hx : x ≠ 0) (hxu : ¬ IsUnit x) :
    Nonempty (ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨u, v, huv⟩ := exists_norm_eq ha x hx (N_eq_zero_of_not_isUnit hxu)
  exact QuaternionAlgebra.nonempty_algEquiv_matrix_of_eq_mul_self_sub ha hb huv

end C8NSplit

open scoped Quaternion

theorem solution
    {F : Type*} [Field F] [NeZero (2 : F)] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (x : ℍ[F, a, b]) (hx : x ≠ 0) (hxu : ¬ IsUnit x) :
    Nonempty (ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) :=
  C8NSplit.main ha hb x hx hxu

end S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit (solution)
