-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9d976358-ee7e-5291-a2f1-c30fda0a80eb

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf

set_option autoImplicit false

open scoped Quaternion

namespace UnitTame

open QuaternionAlgebra Polynomial

variable {a b : ℚ}

theorem re_sq_le_nrd (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b]) : x.re ^ 2 ≤ nrd x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [nrd_mk]
  have h1 : 0 ≤ -a * x1 ^ 2 := mul_nonneg (by linarith) (sq_nonneg x1)
  have h2 : 0 ≤ -b * x2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg x2)
  have h3 : 0 ≤ (a * b) * x3 ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg x3)
  linarith

theorem eq_zero_of_nrd_eq_zero (ha : a < 0) (hb : b < 0) (x : ℍ[ℚ, a, b]) (h : nrd x = 0) : x = 0 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [nrd_mk] at h
  have ha' : 0 < -a := by linarith
  have hb' : 0 < -b := by linarith
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have h0' : 0 ≤ x0 ^ 2 := sq_nonneg x0
  have h1' : 0 ≤ -a * x1 ^ 2 := mul_nonneg ha'.le (sq_nonneg x1)
  have h2' : 0 ≤ -b * x2 ^ 2 := mul_nonneg hb'.le (sq_nonneg x2)
  have h3' : 0 ≤ (a * b) * x3 ^ 2 := mul_nonneg hab.le (sq_nonneg x3)
  have e0 : x0 ^ 2 = 0 := by linarith
  have e1 : -a * x1 ^ 2 = 0 := by linarith
  have e2 : -b * x2 ^ 2 = 0 := by linarith
  have e3 : (a * b) * x3 ^ 2 = 0 := by linarith
  have h0 : x0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e0
  have h1 : x1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp e1).resolve_left ha'.ne')
  have h2 : x2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp e2).resolve_left hb'.ne')
  have h3 : x3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp e3).resolve_left hab.ne')
  subst h0 h1 h2 h3
  rfl

theorem mul_self_eq (u : ℍ[ℚ, a, b]) : u * u = (trd u) • u - ((nrd u : ℚ) : ℍ[ℚ, a, b]) := by
  have h1 : u * (u + star u) = u * u + ((nrd u : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_add, mul_star_eq_coe_nrd]
  rw [add_star_eq_coe_trd, QuaternionAlgebra.mul_coe_eq_smul] at h1
  rw [h1, add_sub_cancel_right]

section Powers
variable (u : ℍ[ℚ, a, b]) (t : ℚ) (hu : u * u = t • u - 1)
include hu

theorem pow_three_eq_neg_one_of (ht : t = 1) : u ^ 3 = -1 := by
  subst ht
  rw [one_smul] at hu
  calc u ^ 3 = u * (u * u) := by rw [pow_succ, pow_two, mul_assoc]
    _ = u * (u - 1) := by rw [hu]
    _ = u * u - u := by rw [mul_sub, mul_one]
    _ = -1 := by rw [hu]; abel

theorem pow_three_eq_one_of (ht : t = -1) : u ^ 3 = 1 := by
  subst ht
  rw [neg_smul, one_smul] at hu
  calc u ^ 3 = u * (u * u) := by rw [pow_succ, pow_two, mul_assoc]
    _ = u * (-u - 1) := by rw [hu]
    _ = -(u * u) - u := by rw [mul_sub, mul_neg, mul_one]
    _ = 1 := by rw [hu]; abel

theorem pow_two_eq_neg_one_of (ht : t = 0) : u ^ 2 = -1 := by
  subst ht
  rw [zero_smul, zero_sub] at hu
  rw [pow_two, hu]

end Powers

theorem exists_monic_aeval_eq_zero {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : ℍ[ℚ, a, b]} (hu : u ∈ Λ) :
    ∃ p : ℤ[X], p.Monic ∧ aeval u (p.map (algebraMap ℤ ℚ)) = 0 := by
  classical
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.fg
  let L : Λ →ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨u * (x : ℍ[ℚ, a, b]), hΛ.mul_mem hu x.2⟩
      map_add' := fun x y => by apply Subtype.ext; simp [mul_add]
      map_smul' := fun n x => by
        apply Subtype.ext
        change u * ((n • x : Λ) : ℍ[ℚ, a, b]) = n • (u * (x : ℍ[ℚ, a, b]))
        rw [Submodule.coe_smul]
        exact mul_smul_comm n u (x : ℍ[ℚ, a, b]) }
  have hL : ∀ x : Λ, ((L x : Λ) : ℍ[ℚ, a, b]) = u * (x : ℍ[ℚ, a, b]) := fun x => rfl
  have hLpow : ∀ (n : ℕ) (x : Λ), (((L ^ n) x : Λ) : ℍ[ℚ, a, b]) = u ^ n * (x : ℍ[ℚ, a, b]) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, Module.End.mul_apply, ih, hL, pow_succ, mul_assoc]
  have key : ∀ (r : ℤ[X]) (x : Λ), ((aeval L r x : Λ) : ℍ[ℚ, a, b]) = aeval u (r.map (algebraMap ℤ ℚ)) * (x : ℍ[ℚ, a, b]) := by
    intro r
    induction r using Polynomial.induction_on' with
    | add p q hp hq => intro x; rw [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq, Polynomial.map_add, map_add, add_mul]
    | monomial n c =>
        intro x
        rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hLpow,
          Polynomial.map_monomial, aeval_monomial, ← Int.cast_smul_eq_zsmul ℚ, Algebra.smul_def, mul_assoc]
        simp
  haveI : Algebra.IsIntegral ℤ (Module.End ℤ Λ) := Module.End.isIntegral
  obtain ⟨p, hp, hev⟩ : IsIntegral ℤ L := Algebra.IsIntegral.isIntegral L
  refine ⟨p, hp, ?_⟩
  have hev' : aeval L p = 0 := hev
  have h := congrArg (fun f : Λ →ₗ[ℤ] Λ => ((f ⟨1, hΛ.one_mem⟩ : Λ) : ℍ[ℚ, a, b])) hev'
  simp only [LinearMap.zero_apply, Submodule.coe_zero] at h
  rw [key] at h
  simpa using h

theorem nrd_sub_one (u : ℍ[ℚ, a, b]) : nrd (u - 1) = nrd u - trd u + 1 := by
  apply QuaternionAlgebra.coe_injective
  have e : ((nrd (u - 1) : ℚ) : ℍ[ℚ, a, b]) = (u - 1) * star (u - 1) := (mul_star_eq_coe_nrd _).symm
  rw [e, star_sub, star_one, QuaternionAlgebra.coe_add, QuaternionAlgebra.coe_sub, ← mul_star_eq_coe_nrd,
    ← add_star_eq_coe_trd, QuaternionAlgebra.coe_one]
  noncomm_ring

theorem nrd_add_one (u : ℍ[ℚ, a, b]) : nrd (u + 1) = nrd u + trd u + 1 := by
  apply QuaternionAlgebra.coe_injective
  have e : ((nrd (u + 1) : ℚ) : ℍ[ℚ, a, b]) = (u + 1) * star (u + 1) := (mul_star_eq_coe_nrd _).symm
  rw [e, star_add, star_one, QuaternionAlgebra.coe_add, QuaternionAlgebra.coe_add, ← mul_star_eq_coe_nrd,
    ← add_star_eq_coe_trd, QuaternionAlgebra.coe_one]
  noncomm_ring

theorem trd_mem_range_int_or {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : ℍ[ℚ, a, b]} (huΛ : u ∈ Λ)
    (hn : nrd u = 1) : (∃ m : ℤ, trd u = (m : ℚ)) ∨ u = 1 ∨ u = -1 := by
  classical
  have hq : u * u = (trd u) • u - 1 := by rw [mul_self_eq, hn, QuaternionAlgebra.coe_one]
  set t : ℚ := trd u with ht

  set q : ℚ[X] := X ^ 2 + (C (-t) * X + C 1) with hqdef
  have hlow : (C (-t) * X + C 1 : ℚ[X]).degree < 2 :=
    (degree_add_le _ _).trans_lt (max_lt ((degree_C_mul_X_le _).trans_lt (by decide)) ((degree_C_le).trans_lt (by decide)))
  have hqm : q.Monic := monic_X_pow_add hlow
  have hqnat : q.natDegree = 2 := by
    rw [hqdef, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rwa [degree_X_pow]
  have hq0 : aeval u q = 0 := by
    simp only [hqdef, map_add, map_mul, aeval_X_pow, aeval_C, aeval_X, map_neg, map_one]
    rw [pow_two, hq, neg_mul, ← Algebra.smul_def]
    abel

  obtain ⟨p, hp, hpu⟩ := exists_monic_aeval_eq_zero hΛ huΛ
  set pQ : ℚ[X] := p.map (algebraMap ℤ ℚ) with hpQ

  set r : ℚ[X] := pQ %ₘ q with hr
  have hr0 : aeval u r = 0 := by rw [hr, aeval_modByMonic_eq_self_of_root hq0]; exact hpu
  by_cases hrz : r = 0
  ·
    left
    have hdvd : q ∣ pQ := (modByMonic_eq_zero_iff_dvd hqm).mp hrz
    obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hp hdvd
    rw [hqm.leadingCoeff, C_1, mul_one] at hg'
    refine ⟨-(g'.coeff 1), ?_⟩
    have hc := congrArg (fun f : ℚ[X] => f.coeff 1) hg'
    simp only [coeff_map] at hc
    have hq1 : q.coeff 1 = -t := by rw [hqdef]; simp [coeff_X_pow, coeff_C, coeff_one]
    rw [hq1] at hc
    have hc' : ((g'.coeff 1 : ℤ) : ℚ) = -t := by simpa using hc
    rw [Int.cast_neg, hc', neg_neg]
  ·
    right
    have hrdeg : r.degree ≤ 1 := by
      have h1 : r.natDegree < q.natDegree := natDegree_lt_natDegree hrz (hr ▸ degree_modByMonic_lt pQ hqm)
      rw [hqnat] at h1
      exact degree_le_of_natDegree_le (Nat.le_of_lt_succ h1)
    have hreq := eq_X_add_C_of_degree_le_one hrdeg
    have hev : (r.coeff 1) • u + (r.coeff 0) • (1 : ℍ[ℚ, a, b]) = 0 := by
      have := hr0
      rw [hreq, map_add, map_mul, aeval_C, aeval_X, aeval_C, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] at this
      exact this
    by_cases hc1 : r.coeff 1 = 0
    · exfalso
      rw [hc1, zero_smul, zero_add, smul_eq_zero, or_iff_left one_ne_zero] at hev
      apply hrz
      rw [hreq, hc1, hev, C_0, zero_mul, zero_add]
    · set c : ℚ := -(r.coeff 0) / r.coeff 1 with hc
      have huc : u = (c : ℍ[ℚ, a, b]) := by
        have e1 : (r.coeff 1) • u = (-(r.coeff 0)) • (1 : ℍ[ℚ, a, b]) := by
          rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hev
        have e2 : u = ((r.coeff 1)⁻¹ * -(r.coeff 0)) • (1 : ℍ[ℚ, a, b]) := by
          rw [← smul_smul, ← e1, smul_smul, inv_mul_cancel₀ hc1, one_smul]
        rw [e2, hc, div_eq_inv_mul, ← Algebra.algebraMap_eq_smul_one]
        rfl
      have hc2 : c ^ 2 = 1 := by rw [← nrd_coe (a := a) (b := b) c, ← huc]; exact hn
      rcases sq_eq_one_iff.mp hc2 with h | h
      · left; rw [huc, h, QuaternionAlgebra.coe_one]
      · right; rw [huc, h, QuaternionAlgebra.coe_neg, QuaternionAlgebra.coe_one]

theorem pow_twelve_eq_one (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (u : ℍ[ℚ, a, b]) (hu : IsUnitOf Λ u) : u ^ 12 = 1 := by
  have hn : nrd u = 1 := (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one ha hb hΛ).2 u hu
  have hq : u * u = (trd u) • u - 1 := by rw [mul_self_eq, hn, QuaternionAlgebra.coe_one]
  rcases trd_mem_range_int_or hΛ hu.1 hn with ⟨m, hm⟩ | h1 | h1
  ·
    have hre : u.re ^ 2 ≤ 1 := hn ▸ re_sq_le_nrd ha hb u
    have ht2 : (trd u) ^ 2 ≤ 4 := by rw [show trd u = 2 * u.re from rfl]; nlinarith
    rw [hm] at ht2 hq
    have hm2 : m ^ 2 ≤ 4 := by exact_mod_cast ht2
    have hmle : m ≤ 2 := by nlinarith
    have hmge : -2 ≤ m := by nlinarith
    interval_cases m
    ·
      have h0 : nrd (u + 1) = 0 := by rw [nrd_add_one, hn, hm]; norm_num
      have : u = -1 := eq_neg_of_add_eq_zero_left (eq_zero_of_nrd_eq_zero ha hb _ h0)
      rw [this]; norm_num
    · have h3 := pow_three_eq_one_of u (((-1 : ℤ) : ℚ)) hq (by norm_num)
      calc u ^ 12 = (u ^ 3) ^ 4 := by rw [← pow_mul]
        _ = 1 := by rw [h3, one_pow]
    · have h2 := pow_two_eq_neg_one_of u (((0 : ℤ) : ℚ)) hq (by norm_num)
      calc u ^ 12 = (u ^ 2) ^ 6 := by rw [← pow_mul]
        _ = 1 := by rw [h2]; norm_num
    · have h3 := pow_three_eq_neg_one_of u (((1 : ℤ) : ℚ)) hq (by norm_num)
      calc u ^ 12 = (u ^ 3) ^ 4 := by rw [← pow_mul]
        _ = 1 := by rw [h3]; norm_num
    ·
      have h0 : nrd (u - 1) = 0 := by rw [nrd_sub_one, hn, hm]; norm_num
      have : u = 1 := sub_eq_zero.mp (eq_zero_of_nrd_eq_zero ha hb _ h0)
      rw [this, one_pow]
  · rw [h1, one_pow]
  · rw [h1]; norm_num

def unitSubgroup (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) : Subgroup (ℍ[ℚ, a, b])ˣ where
  carrier := {x | (x : ℍ[ℚ, a, b]) ∈ Λ ∧ ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ}
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact hΛ.mul_mem hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact hΛ.mul_mem hy.2 hx.2
  one_mem' := ⟨by rw [Units.val_one]; exact hΛ.one_mem, by rw [inv_one, Units.val_one]; exact hΛ.one_mem⟩
  inv_mem' := by
    intro x hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

noncomputable def unitEquiv (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) :
    {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} ≃ unitSubgroup Λ hΛ where
  toFun u := ⟨⟨u.1, u.2.2.choose, u.2.2.choose_spec.2.1, u.2.2.choose_spec.2.2⟩, ⟨u.2.1, u.2.2.choose_spec.1⟩⟩
  invFun x := ⟨(x.1 : ℍ[ℚ, a, b]), ⟨x.2.1, ((x.1⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), x.2.2, x.1.mul_inv, x.1.inv_mul⟩⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Units.ext; rfl

theorem not_dvd_card (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} := by
  classical
  intro hdvd
  haveI : Finite {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} := (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one ha hb hΛ).1
  haveI : Finite (unitSubgroup Λ hΛ) := Finite.of_equiv _ (unitEquiv Λ hΛ)
  haveI : Fintype (unitSubgroup Λ hΛ) := Fintype.ofFinite _
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_congr (unitEquiv Λ hΛ), Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
  have hxu : IsUnitOf Λ ((x : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) :=
    ⟨x.2.1, (((x : (ℍ[ℚ, a, b])ˣ)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), x.2.2, (x : (ℍ[ℚ, a, b])ˣ).mul_inv, (x : (ℍ[ℚ, a, b])ˣ).inv_mul⟩
  have h12 : ((x : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ^ 12 = 1 := pow_twelve_eq_one ha hb hΛ _ hxu
  have hx12 : x ^ 12 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, h12, Subgroup.coe_one, Units.val_one]
  have hdiv : p ∣ 12 := by rw [← hx]; exact orderOf_dvd_of_pow_eq_one hx12
  have hple : p ≤ 12 := Nat.le_of_dvd (by norm_num) hdiv
  interval_cases p <;> simp_all (config := {decide := true})

end UnitTame

open scoped Quaternion in
theorem solution
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (∀ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf Λ u → u ^ 12 = 1) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card {u : ℍ[ℚ, a, b] // QuaternionAlgebra.IsUnitOf Λ u} :=
  ⟨fun u hu => UnitTame.pow_twelve_eq_one ha hb hΛ u hu, fun p hp hp5 => UnitTame.not_dvd_card ha hb hΛ p hp hp5⟩

end S_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_pow_twelve_eq_one_and_not_dvd_natCard_isUnitOf (solution)
