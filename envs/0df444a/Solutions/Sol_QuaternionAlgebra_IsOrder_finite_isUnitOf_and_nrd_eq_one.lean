-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f4d808e3-4027-5167-9d37-7d1b03485dc6

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_sq_sub_trd_mul_add_nrd
import Theorems.Thm_QuaternionAlgebra_finite_embeddingDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one

set_option autoImplicit false
open scoped Quaternion

namespace Ws18Orbit

open Quaternion QuaternionAlgebra Polynomial

variable {a b : ℚ}

def subalg {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : Subalgebra ℤ ℍ[ℚ, a, b] where
  carrier := Λ
  mul_mem' := fun hx hy => hΛ.mul_mem hx hy
  one_mem' := hΛ.one_mem
  add_mem' := fun hx hy => Λ.add_mem hx hy
  zero_mem' := Λ.zero_mem
  algebraMap_mem' := fun k => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Λ.smul_mem k hΛ.one_mem

theorem subalg_toSubmodule {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (subalg hΛ).toSubmodule = Λ := by
  ext x; exact Iff.rfl

theorem isIntegral_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) : IsIntegral ℤ x :=
  IsIntegral.of_mem_of_fg (subalg hΛ) (by rw [subalg_toSubmodule]; exact hΛ.fg) x hx

theorem exists_int_of_smul_one_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (r : ℚ)
    (hr : r • (1 : ℍ[ℚ, a, b]) ∈ Λ) : ∃ k : ℤ, (k : ℚ) = r := by
  have hi : IsIntegral ℤ (algebraMap ℚ ℍ[ℚ, a, b] r) := by
    rw [Algebra.algebraMap_eq_smul_one]; exact isIntegral_of_mem hΛ hr
  rw [isIntegral_algebraMap_iff (algebraMap ℚ ℍ[ℚ, a, b]).injective] at hi
  exact IsIntegrallyClosed.isIntegral_iff.mp hi

theorem coe_eq_smul_one' (r : ℚ) : ((r : ℚ) : ℍ[ℚ, a, b]) = r • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp

theorem smul_one_add_smul_eq_zero {x : ℍ[ℚ, a, b]} (hnc : ¬ (x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0))
    {c d : ℚ} (h : c • (1 : ℍ[ℚ, a, b]) + d • x = 0) : c = 0 ∧ d = 0 := by
  by_cases hd : d = 0
  · subst hd
    rw [zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right one_ne_zero, rfl⟩
  · exfalso
    apply hnc
    have hx : x = (-(d⁻¹ * c)) • (1 : ℍ[ℚ, a, b]) := by
      have : d • x = -(c • (1 : ℍ[ℚ, a, b])) := eq_neg_of_add_eq_zero_right h
      calc x = d⁻¹ • (d • x) := by rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, neg_smul]
    refine ⟨?_, ?_, ?_⟩ <;> · rw [hx]; simp

theorem aeval_charpoly (x : ℍ[ℚ, a, b]) :
    aeval x (X ^ 2 - C (trd x) * X + C (nrd x) : ℚ[X]) = 0 := by
  have h := QuaternionAlgebra.sq_sub_trd_mul_add_nrd x
  simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← coe_eq_smul_one',
    ← coe_eq_smul_one', sq]
  exact h

theorem monic_charpoly (t n : ℚ) : (X ^ 2 - C t * X + C n : ℚ[X]).Monic := by
  have h : (X ^ 2 - C t * X + C n : ℚ[X]) = X ^ 2 + (C (-t) * X + C n) := by
    simp only [map_neg, neg_mul]; ring
  rw [h]
  refine (monic_X_pow 2).add_of_left ?_
  refine (degree_add_le _ _).trans_lt ?_
  rw [degree_X_pow]
  refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ((degree_C_le).trans_lt (by norm_num))

theorem exists_int_trd_nrd {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) : ∃ t n : ℤ, trd x = t ∧ nrd x = n := by
  by_cases hc : x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  ·
    obtain ⟨h1, h2, h3⟩ := hc
    have hxe : x = x.re • (1 : ℍ[ℚ, a, b]) := by
      ext <;> simp [h1, h2, h3]
    obtain ⟨k, hk⟩ := exists_int_of_smul_one_mem hΛ x.re (hxe ▸ hx)
    refine ⟨2 * k, k ^ 2, ?_, ?_⟩
    · simp [trd, ← hk]
    · rw [nrd, h1, h2, h3, ← hk]; push_cast; ring
  · obtain ⟨p, hp, hpx⟩ := isIntegral_of_mem hΛ hx
    set m : ℚ[X] := X ^ 2 - C (trd x) * X + C (nrd x) with hm
    have hmm : m.Monic := monic_charpoly _ _
    set P : ℚ[X] := p.map (algebraMap ℤ ℚ) with hP
    have hPx : aeval x P = 0 := by rw [hP, aeval_map_algebraMap]; exact hpx

    have hr : P %ₘ m = 0 := by
      set r := P %ₘ m with hrdef
      have hdeg : r.degree ≤ 1 := by
        have := degree_modByMonic_lt P hmm
        have hm2 : m.degree = 2 := by
          rw [hm]; compute_degree!
        rw [hm2] at this
        exact Order.le_of_lt_succ this
      have hr1 := eq_X_add_C_of_degree_le_one hdeg
      have hrx : aeval x r = 0 := by
        have := modByMonic_add_div P m
        apply_fun aeval x at this
        rw [map_add, map_mul, aeval_charpoly, zero_mul, add_zero, hPx] at this
        exact this
      rw [hr1] at hrx
      simp only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul] at hrx
      rw [add_comm] at hrx
      obtain ⟨h0, h1⟩ := smul_one_add_smul_eq_zero hc hrx
      rw [hr1, h0, h1]; simp
    have hdvd : m ∣ p.map (algebraMap ℤ ℚ) := (modByMonic_eq_zero_iff_dvd hmm).mp hr
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hp hdvd
    rw [hmm.leadingCoeff, C_1, mul_one] at hg
    refine ⟨-g.coeff 1, g.coeff 0, ?_, ?_⟩
    · have := congrArg (fun q : ℚ[X] => q.coeff 1) hg
      simp only [coeff_map, hm, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one,
        coeff_C, if_neg (one_ne_zero)] at this
      norm_num at this
      push_cast; linarith
    · have := congrArg (fun q : ℚ[X] => q.coeff 0) hg
      simp only [coeff_map, hm, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_zero,
        coeff_C_zero, mul_zero, sub_zero] at this
      norm_num at this
      exact this.symm

end Ws18Orbit

namespace Ws18Orbit

open Quaternion QuaternionAlgebra

variable {a b : ℚ}

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_nonneg (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b]) : 0 ≤ nrd x := by
  rw [nrd]
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  nlinarith [sq_nonneg x.re, sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK,
    mul_nonneg (neg_nonneg.mpr ha.le) (sq_nonneg x.imI), mul_nonneg (neg_nonneg.mpr hb.le) (sq_nonneg x.imJ),
    mul_nonneg hab.le (sq_nonneg x.imK)]

theorem re_sq_le_nrd (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b]) : x.re ^ 2 ≤ nrd x := by
  rw [nrd]
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  nlinarith [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK,
    mul_nonneg (neg_nonneg.mpr ha.le) (sq_nonneg x.imI), mul_nonneg (neg_nonneg.mpr hb.le) (sq_nonneg x.imJ),
    mul_nonneg hab.le (sq_nonneg x.imK)]

theorem nrd_eq_one_of_isUnitOf (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : IsOrder Λ) {u : ℍ[ℚ, a, b]} (hu : IsUnitOf Λ u) : nrd u = 1 := by
  obtain ⟨huΛ, v, hvΛ, huv, -⟩ := hu
  obtain ⟨-, m, -, hm⟩ := exists_int_trd_nrd hΛ huΛ
  obtain ⟨-, m', -, hm'⟩ := exists_int_trd_nrd hΛ hvΛ
  have h1 : nrd u * nrd v = 1 := by rw [← nrd_mul', huv, nrd_one]
  rw [hm, hm'] at h1
  have h1' : m * m' = 1 := by exact_mod_cast h1
  have hm0 : 0 ≤ m := by
    have := nrd_nonneg ha hb u; rw [hm] at this; exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1' with h | h
  · rw [hm, h]; norm_num
  · omega

theorem isQuadraticDatum_of_isUnitOf (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : IsOrder Λ) {u : ℍ[ℚ, a, b]} (hu : IsUnitOf Λ u) :
    ∃ t : ℤ, -2 ≤ t ∧ t ≤ 2 ∧ IsQuadraticDatum t 1 u := by
  obtain ⟨t, m, ht, hm⟩ := exists_int_trd_nrd hΛ hu.1
  have h1 := nrd_eq_one_of_isUnitOf ha hb hΛ hu
  refine ⟨t, ?_, ?_, ?_⟩
  · have := re_sq_le_nrd ha hb u
    rw [h1] at this
    have htr : (t : ℚ) = 2 * u.re := by rw [← ht]; rfl
    have : (t : ℚ) ^ 2 ≤ 4 := by rw [htr]; nlinarith
    have : (t : ℤ) ^ 2 ≤ 4 := by exact_mod_cast this
    nlinarith
  · have := re_sq_le_nrd ha hb u
    rw [h1] at this
    have htr : (t : ℚ) = 2 * u.re := by rw [← ht]; rfl
    have : (t : ℚ) ^ 2 ≤ 4 := by rw [htr]; nlinarith
    have : (t : ℤ) ^ 2 ≤ 4 := by exact_mod_cast this
    nlinarith
  · rw [IsQuadraticDatum]
    have h := QuaternionAlgebra.sq_sub_trd_mul_add_nrd u
    rw [ht, h1, coe_eq_smul_one', coe_eq_smul_one', smul_mul_assoc, one_mul] at h
    push_cast
    exact h

theorem finite_isUnitOf (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    Finite {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} := by
  classical
  haveI : ∀ t : ℤ, Finite (EmbeddingDatum Λ t 1) := fun t =>
    QuaternionAlgebra.finite_embeddingDatum ha hb Λ hΛ.fg t 1
  let T : Type := {t : ℤ // -2 ≤ t ∧ t ≤ 2}
  haveI : Finite T := by
    refine Finite.of_injective (fun t : T => (⟨(t.1 + 2).toNat, by have := t.2; omega⟩ : Fin 5)) ?_
    intro s t h
    have := congrArg Fin.val h
    simp only at this
    exact Subtype.ext (by have := s.2; have := t.2; omega)
  let φ : {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} → (Σ t : T, EmbeddingDatum Λ t.1 1) := fun u =>
    let h := isQuadraticDatum_of_isUnitOf ha hb hΛ u.2
    ⟨⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩, ⟨u.1, u.2.1, h.choose_spec.2.2⟩⟩
  refine Finite.of_injective φ ?_
  intro u v h
  have := congrArg (fun s => (s.2.1 : ℍ[ℚ, a, b])) h
  exact Subtype.ext this

end Ws18Orbit

open scoped Quaternion in
theorem solution
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    Finite {u : ℍ[ℚ, a, b] // QuaternionAlgebra.IsUnitOf Λ u} ∧
      ∀ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf Λ u → QuaternionAlgebra.nrd u = 1 :=
  ⟨Ws18Orbit.finite_isUnitOf ha hb hΛ, fun _ hu => Ws18Orbit.nrd_eq_one_of_isUnitOf ha hb hΛ hu⟩

end S_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one (solution)
