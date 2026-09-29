-- Prove2me | solution 1 for WeierstrassCurve.kohelQuotient_kernelPolynomial_eq_veluQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7ffb4d6f-46a0-5c62-a307-1c010baf24ab

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "b₂ Ψ₂Sq toAffine b₆ b₄ veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_eq_veluQuotientOfSums kernelPolynomial kernelPolynomial_cons monic_kernelPolynomial natDegree_kernelPolynomial kohelT kohelW kohelQuotient"
p2m_open "WeierstrassCurve"

namespace KohelVelu

variable {R : Type*} [CommRing R]

theorem natDegree_X_sub_C_mul [Nontrivial R] {h : R[X]} (hh : h.Monic) (x : R) :
    ((X - C x) * h).natDegree = h.natDegree + 1 := by
  rw [(monic_X_sub_C x).natDegree_mul hh, natDegree_X_sub_C, add_comm]

theorem rootESymm_X_sub_C_mul_succ [Nontrivial R] {h : R[X]} (hh : h.Monic) (x : R) (k : ℕ) :
    ((X - C x) * h).rootESymm (k + 1) = h.rootESymm (k + 1) + x * h.rootESymm k := by
  have hnd := natDegree_X_sub_C_mul hh x
  rcases lt_trichotomy k h.natDegree with hk | rfl | hk
  ·
    rw [rootESymm_of_le (by omega : k + 1 ≤ ((X - C x) * h).natDegree),
      rootESymm_of_le (by omega : k + 1 ≤ h.natDegree), rootESymm_of_le hk.le, hnd]
    obtain ⟨m, hm⟩ : ∃ m, h.natDegree - (k + 1) = m := ⟨_, rfl⟩
    have h1 : h.natDegree + 1 - (k + 1) = m + 1 := by omega
    have h2 : h.natDegree - k = m + 1 := by omega
    rw [h1, hm, h2, coeff_X_sub_C_mul]
    ring
  ·
    rw [rootESymm_of_le (by omega : h.natDegree + 1 ≤ ((X - C x) * h).natDegree),
      rootESymm_of_lt (Nat.lt_succ_self _), rootESymm_of_le le_rfl, hnd, Nat.sub_self, Nat.sub_self]
    have : ((X - C x) * h).coeff 0 = -(x * h.coeff 0) := by
      simp [sub_mul]
    rw [this]
    ring
  ·
    rw [rootESymm_of_lt (by omega), rootESymm_of_lt (by omega), rootESymm_of_lt hk]
    ring

theorem rootESymm_zero_of_monic {h : R[X]} (hh : h.Monic) : h.rootESymm 0 = 1 := by
  rw [rootESymm_zero_right, hh.leadingCoeff]

theorem rootPowerSumOne_X_sub_C_mul [Nontrivial R] {h : R[X]} (hh : h.Monic) (x : R) :
    ((X - C x) * h).rootPowerSumOne = h.rootPowerSumOne + x := by
  simp only [rootPowerSumOne, rootESymm_X_sub_C_mul_succ hh, rootESymm_zero_of_monic hh, mul_one]

theorem rootPowerSumTwo_X_sub_C_mul [Nontrivial R] {h : R[X]} (hh : h.Monic) (x : R) :
    ((X - C x) * h).rootPowerSumTwo = h.rootPowerSumTwo + x ^ 2 := by
  simp only [rootPowerSumTwo, rootESymm_X_sub_C_mul_succ hh, rootESymm_zero_of_monic hh]
  ring

theorem rootPowerSumThree_X_sub_C_mul [Nontrivial R] {h : R[X]} (hh : h.Monic) (x : R) :
    ((X - C x) * h).rootPowerSumThree = h.rootPowerSumThree + x ^ 3 := by
  simp only [rootPowerSumThree, rootESymm_X_sub_C_mul_succ hh, rootESymm_zero_of_monic hh]
  ring

theorem powerSums_kernelPolynomial [Nontrivial R] (S : Finset (R × R)) :
    (kernelPolynomial S).rootPowerSumOne = ∑ P ∈ S, P.1 ∧
      (kernelPolynomial S).rootPowerSumTwo = ∑ P ∈ S, P.1 ^ 2 ∧
        (kernelPolynomial S).rootPowerSumThree = ∑ P ∈ S, P.1 ^ 3 := by
  induction S using Finset.cons_induction with
  | empty =>
    simp [rootPowerSumOne, rootPowerSumTwo, rootPowerSumThree]
  | cons P S hP ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hmon := monic_kernelPolynomial S
    rw [kernelPolynomial_cons hP, Finset.sum_cons, Finset.sum_cons, Finset.sum_cons,
      rootPowerSumOne_X_sub_C_mul hmon, rootPowerSumTwo_X_sub_C_mul hmon,
      rootPowerSumThree_X_sub_C_mul hmon, ih1, ih2, ih3]
    exact ⟨add_comm _ _, add_comm _ _, add_comm _ _⟩

theorem veluW_eq_of_equation (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) :
    W.veluW x y = 10 * x ^ 3 + 2 * W.b₂ * x ^ 2 + 3 * W.b₄ * x + W.b₆ := by
  rw [veluW, W.veluU_eq_Ψ₂Sq_eval h, veluT_eq]
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem kohelT_kernelPolynomial [Nontrivial R] (W : WeierstrassCurve R) (S : Finset (R × R)) :
    W.kohelT (kernelPolynomial S) = W.veluTSum S := by
  obtain ⟨h1, h2, -⟩ := powerSums_kernelPolynomial S
  rw [kohelT, h1, h2, natDegree_kernelPolynomial, veluTSum]
  simp only [veluT_eq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

theorem kohelW_kernelPolynomial [Nontrivial R] (W : WeierstrassCurve R) (S : Finset (R × R))
    (hS : ∀ P ∈ S, W.toAffine.Equation P.1 P.2) :
    W.kohelW (kernelPolynomial S) = W.veluWSum S := by
  obtain ⟨h1, h2, h3⟩ := powerSums_kernelPolynomial S
  rw [kohelW, h1, h2, h3, natDegree_kernelPolynomial, veluWSum,
    Finset.sum_congr rfl fun P hP => veluW_eq_of_equation W (hS P hP)]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

theorem main (W : WeierstrassCurve R) (S : Finset (R × R))
    (hS : ∀ P ∈ S, W.toAffine.Equation P.1 P.2) :
    W.kohelQuotient (kernelPolynomial S) = W.veluQuotient S := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · ext <;> exact Subsingleton.elim _ _
  rw [kohelQuotient, veluQuotient_eq_veluQuotientOfSums, kohelT_kernelPolynomial,
    kohelW_kernelPolynomial W S hS]

end KohelVelu

end WeierstrassCurve

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))
    (hS : ∀ P ∈ S, W.toAffine.Equation P.1 P.2) :
    W.kohelQuotient (WeierstrassCurve.kernelPolynomial S) = W.veluQuotient S :=
  WeierstrassCurve.KohelVelu.main W S hS

end S_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient
end P2MW
export P2MW.S_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient (solution)
