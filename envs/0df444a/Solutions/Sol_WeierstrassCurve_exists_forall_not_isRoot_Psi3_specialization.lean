-- Prove2me | solution 1 for WeierstrassCurve.exists_forall_not_isRoot_Psi3_specialization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e0d255ed-2b9b-5fbe-974c-f5fe96b664e9

import Theorems.Thm_Polynomial_exists_forall_not_isRoot_of_weighted
import Theorems.Thm_WeierstrassCurve_separable_Psi3
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization

set_option autoImplicit false

open Polynomial

namespace M4cP1D1

theorem psi3_short {S : Type*} [CommRing S] (a b : S) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve S).Ψ₃ = C 3 * X ^ 4 + C (6 * a) * X ^ 2 + C (12 * b) * X
      + C (-a ^ 2) := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_zero]
  ring

theorem coeff_psi3_short {S : Type*} [CommRing S] (a b : S) (k : ℕ) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve S).Ψ₃.coeff k =
      if k = 4 then 3 else if k = 2 then 6 * a else if k = 1 then 12 * b else if k = 0 then -a ^ 2
        else 0 := by
  rw [psi3_short]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  rcases k with _ | _ | _ | _ | _ | k <;> simp

theorem natDegree_psi3_le (a b : ℚ[X]) :
    ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).natDegree ≤ 4 := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  rw [coeff_psi3_short]
  have hk' : 4 < k := by exact_mod_cast hk
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem coeff_psi3_coeff_eq_zero (a b : ℚ[X]) (ha : a.natDegree ≤ 20) (hb : b.natDegree ≤ 30)
    (k j : ℕ) (hkj : 10 * (4 - k) < j) :
    (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff k).coeff j = 0 := by
  rw [coeff_psi3_short]
  split_ifs with h4 h2 h1 h0
  ·
    subst h4
    have hj : j ≠ 0 := by omega
    rw [show (3 : ℚ[X]) = C 3 from rfl, coeff_C, if_neg hj]
  ·
    subst h2
    refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ (show 20 < j by omega))
    rw [show (6 : ℚ[X]) = C 6 from rfl]
    exact (natDegree_C_mul_le _ _).trans ha
  ·
    subst h1
    refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ (show 30 < j by omega))
    rw [show (12 : ℚ[X]) = C 12 from rfl]
    exact (natDegree_C_mul_le _ _).trans hb
  ·
    subst h0
    refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ (show 40 < j by omega))
    rw [natDegree_neg]
    exact natDegree_pow_le.trans (by omega)
  · exact coeff_zero j

theorem coeff_psi3_four (a b : ℚ[X]) :
    (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff 4).coeff 0 = 3 := by
  rw [coeff_psi3_short, if_pos rfl, show (3 : ℚ[X]) = C 3 from rfl, coeff_C_zero]

theorem topForm_psi3 (a b : ℚ[X]) (ha : a.natDegree ≤ 20) :
    (∑ k ∈ Finset.range (4 + 1),
        C ((((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff k).coeff (10 * (4 - k))) * X ^ k
      : ℚ[X]) = (⟨0, 0, 0, a.coeff 20, b.coeff 30⟩ : WeierstrassCurve ℚ).Ψ₃ := by

  have c0 : (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff 0).coeff 40 = -a.coeff 20 ^ 2 := by
    rw [coeff_psi3_short]
    simp only [show (0 : ℕ) ≠ 4 by decide, show (0 : ℕ) ≠ 2 by decide, show (0 : ℕ) ≠ 1 by decide,
      if_false, if_true, coeff_neg]
    rw [show (40 : ℕ) = 2 * 20 by norm_num, coeff_pow_of_natDegree_le ha]
  have c1 : (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff 1).coeff 30 = 12 * b.coeff 30 := by
    rw [coeff_psi3_short]
    simp only [show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 2 by decide, if_false, if_true]
    rw [show (12 : ℚ[X]) = C 12 from rfl, coeff_C_mul]
  have c2 : (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff 2).coeff 20 = 6 * a.coeff 20 := by
    rw [coeff_psi3_short]
    simp only [show (2 : ℕ) ≠ 4 by decide, if_false, if_true]
    rw [show (6 : ℚ[X]) = C 6 from rfl, coeff_C_mul]
  have c3 : (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff 3).coeff 10 = 0 := by
    rw [coeff_psi3_short]
    simp only [show (3 : ℕ) ≠ 4 by decide, show (3 : ℕ) ≠ 2 by decide, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 0 by decide, if_false, coeff_zero]
  have c4 : (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff 4).coeff 0 = 3 :=
    coeff_psi3_four a b
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only [Nat.sub_self, Nat.mul_zero]
  rw [c0, c1, c2, c3, c4, psi3_short]
  simp only [map_ofNat, map_neg, map_mul, map_pow, map_zero]
  ring

theorem map_psi3_eval (a b : ℚ[X]) (t₀ : ℚ) :
    ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).map (evalRingHom t₀) =
      (⟨0, 0, 0, a.eval t₀, b.eval t₀⟩ : WeierstrassCurve ℚ).Ψ₃ := by
  rw [← WeierstrassCurve.map_Ψ₃]
  congr 1
  simp [WeierstrassCurve.map]

theorem delta_short (A B : ℚ) : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℚ).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

end M4cP1D1

set_option autoImplicit false

open Polynomial

namespace M4cP1D1

theorem exists_forall_not_isRoot_psi3_specialization (a b : ℚ[X]) (ha : a.natDegree ≤ 20)
    (hb : b.natDegree ≤ 30) (hinf : 4 * a.coeff 20 ^ 3 + 27 * b.coeff 30 ^ 2 ≠ 0)
    (hroot : ∀ g : ℚ[X], (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃.eval g ≠ 0)
    (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) :
    ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ,
      ¬ (⟨0, 0, 0, a.eval ((M : ℚ) * m), b.eval ((M : ℚ) * m)⟩ : WeierstrassCurve ℚ).Ψ₃.IsRoot x := by
  have hsep : (∑ k ∈ Finset.range (4 + 1),
      C ((((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃).coeff k).coeff (10 * (4 - k))) * X ^ k :
        ℚ[X]).Separable := by
    rw [topForm_psi3 a b ha]
    refine WeierstrassCurve.separable_Psi3 _ ?_ (by norm_num)
    rw [delta_short]
    exact mul_ne_zero (by norm_num) hinf
  obtain ⟨m, hm, hnone⟩ := exists_forall_not_isRoot_of_weighted 4 10
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ[X]).Ψ₃ (natDegree_psi3_le a b)
    (coeff_psi3_coeff_eq_zero a b ha hb) (by rw [coeff_psi3_four]; norm_num) hsep hroot M hM m₀
  exact ⟨m, hm, fun x hx => hnone x (by rwa [map_psi3_eval])⟩

end M4cP1D1

open Polynomial in
theorem solution (a b : Polynomial ℚ) (ha : a.natDegree ≤ 20) (hb : b.natDegree ≤ 30)
    (hinf : 4 * a.coeff 20 ^ 3 + 27 * b.coeff 30 ^ 2 ≠ 0)
    (hroot : ∀ g : Polynomial ℚ, (⟨0, 0, 0, a, b⟩ : WeierstrassCurve (Polynomial ℚ)).Ψ₃.eval g ≠ 0)
    (M : ℕ) (hM : M ≠ 0) (m₀ : ℕ) :
    ∃ m : ℕ, m₀ ≤ m ∧ ∀ x : ℚ,
      ¬ (⟨0, 0, 0, a.eval ((M : ℚ) * m), b.eval ((M : ℚ) * m)⟩ : WeierstrassCurve ℚ).Ψ₃.IsRoot x :=
  M4cP1D1.exists_forall_not_isRoot_psi3_specialization a b ha hb hinf hroot M hM m₀

end S_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization
end P2MW
export P2MW.S_WeierstrassCurve_exists_forall_not_isRoot_Psi3_specialization (solution)
