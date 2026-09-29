-- Prove2me | solution 1 for QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b17437a9-9de2-5c48-b73d-274e4d195a5c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra IsDedekindDomain NumberField

namespace KcSplitN

theorem exists_matrixUnits_of_surjective_of_ker_isNilpotent
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e u v : S} (he : IsIdempotentElem e) (heu : e * u = u) (hue : u * e = 0)
    (hve : v * e = v) (hev : e * v = 0) (huv : u * v = e) (hvu : v * u = 1 - e) :
    ∃ e' u' v' : R, IsIdempotentElem e' ∧ e' * u' = u' ∧ u' * e' = 0 ∧
      v' * e' = v' ∧ e' * v' = 0 ∧ u' * v' = e' ∧ v' * u' = 1 - e' := by
  obtain ⟨e', he', hfe⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f hker e (hf e) he
  obtain ⟨u₀, hu₀⟩ := hf u
  obtain ⟨v₀, hv₀⟩ := hf v

  set u₁ : R := e' * u₀ * (1 - e') with hu₁
  set v₁ : R := (1 - e') * v₀ * e' with hv₁
  have h1e : (1 - e') * e' = 0 := by rw [sub_mul, one_mul, he'.eq, sub_self]
  have he1 : e' * (1 - e') = 0 := by rw [mul_sub, mul_one, he'.eq, sub_self]
  have heu₁ : e' * u₁ = u₁ := by rw [hu₁, ← mul_assoc, ← mul_assoc, he'.eq]
  have hu₁1 : u₁ * (1 - e') = u₁ := by rw [hu₁, mul_assoc, (he'.one_sub).eq]
  have hu₁e : u₁ * e' = 0 := by rw [hu₁, mul_assoc, h1e, mul_zero]
  have hv₁e : v₁ * e' = v₁ := by rw [hv₁, mul_assoc, he'.eq]
  have h1v₁ : (1 - e') * v₁ = v₁ := by rw [hv₁, ← mul_assoc, ← mul_assoc, (he'.one_sub).eq]
  have hev₁ : e' * v₁ = 0 := by rw [hv₁, ← mul_assoc, ← mul_assoc, he1, zero_mul, zero_mul]
  have hfu₁ : f u₁ = u := by
    rw [hu₁, map_mul, map_mul, map_sub, map_one, hfe, hu₀, heu, mul_sub, mul_one, hue, sub_zero]
  have hfv₁ : f v₁ = v := by
    rw [hv₁, map_mul, map_mul, map_sub, map_one, hfe, hv₀, sub_mul, one_mul, hev, sub_zero, hve]

  set n : R := u₁ * v₁ - e' with hn
  have hfn : f n = 0 := by rw [hn, map_sub, map_mul, hfu₁, hfv₁, huv, hfe, sub_self]
  have hnil : IsNilpotent n := hker n (by rwa [RingHom.mem_ker])
  have hen : e' * n = n := by rw [hn, mul_sub, ← mul_assoc, heu₁, he'.eq]
  obtain ⟨w, hw⟩ := hnil.isUnit_one_add
  have hwz : (1 + n) * (↑w⁻¹ : R) = 1 := by rw [← hw, Units.mul_inv]
  have hfz : f (↑w⁻¹ : R) = 1 := by
    have h := congrArg f hwz
    rwa [map_mul, map_add, map_one, hfn, add_zero, one_mul] at h

  set v' : R := v₁ * ↑w⁻¹ * e' with hv'
  have huv₁ : u₁ * v₁ = e' * (1 + n) := by rw [mul_add, mul_one, hen, hn, add_sub_cancel]
  have huv' : u₁ * v' = e' := by
    rw [hv', ← mul_assoc, ← mul_assoc, huv₁, mul_assoc e', hwz, mul_one, he'.eq]
  have hv'e : v' * e' = v' := by rw [hv', mul_assoc, he'.eq]
  have hev' : e' * v' = 0 := by rw [hv', ← mul_assoc, ← mul_assoc, hev₁, zero_mul, zero_mul]
  have h1v' : (1 - e') * v' = v' := by rw [sub_mul, one_mul, hev', sub_zero]
  have hfv' : f v' = v := by rw [hv', map_mul, map_mul, hfv₁, hfz, hfe, mul_one, hve]
  refine ⟨e', u₁, v', he', heu₁, hu₁e, hv'e, hev', huv', ?_⟩

  have hx : IsIdempotentElem (v' * u₁) := by
    change v' * u₁ * (v' * u₁) = v' * u₁
    rw [show v' * u₁ * (v' * u₁) = v' * ((u₁ * v') * u₁) by simp only [mul_assoc], huv', heu₁]
  have h1x : (1 - e') * (v' * u₁) = v' * u₁ := by rw [← mul_assoc, h1v']
  have hx1 : v' * u₁ * (1 - e') = v' * u₁ := by rw [mul_assoc, hu₁1]
  have hy : IsIdempotentElem (1 - e' - v' * u₁) := by
    change (1 - e' - v' * u₁) * (1 - e' - v' * u₁) = 1 - e' - v' * u₁
    rw [sub_mul (1 - e'), mul_sub (1 - e') (1 - e'), mul_sub (v' * u₁) (1 - e'), (he'.one_sub).eq, h1x, hx1,
      hx.eq, sub_self, sub_zero]
  have hfy : f (1 - e' - v' * u₁) = 0 := by
    rw [map_sub, map_sub, map_one, map_mul, hfe, hfu₁, hfv', hvu, sub_self]
  have hy0 : 1 - e' - v' * u₁ = 0 :=
    hy.eq_zero_of_isNilpotent (hker _ (by rwa [RingHom.mem_ker]))
  exact (sub_eq_zero.mp hy0).symm

theorem nonempty_ringEquiv_matrix_of_matrixUnits
    {K R : Type*} [CommRing K] [Ring R] [Finite R] {n : ℕ}
    (c : K →+* R) (hc : ∀ (k : K) (x : R), c k * x = x * c k) (hcinj : Function.Injective c)
    (E : Fin n → Fin n → R) (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (hE1 : ∑ i, E i i = 1) (hcard : Nat.card R = Nat.card K ^ (n * n)) :
    Nonempty (R ≃+* Matrix (Fin n) (Fin n) K) := by
  classical

  let θ : Matrix (Fin n) (Fin n) K → R := fun M => ∑ i, ∑ j, c (M i j) * E i j
  have hθ : ∀ M : Matrix (Fin n) (Fin n) K, θ M = ∑ i, ∑ j, c (M i j) * E i j := fun _ => rfl

  have hrow : ∀ (M : Matrix (Fin n) (Fin n) K) (a i : Fin n),
      E a i * θ M = ∑ l, c (M i l) * E a l := by
    intro M a i
    rw [hθ, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    have h : ∀ k l : Fin n, E a i * (c (M k l) * E k l) = if i = k then c (M k l) * E a l else 0 := by
      intro k l
      rw [← mul_assoc, ← hc (M k l) (E a i), mul_assoc, hE, mul_ite, mul_zero]
    simp_rw [h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

  have hcol : ∀ (x : K) (a l j b : Fin n),
      c x * E a l * E j b = if l = j then c x * E a b else 0 := by
    intro x a l j b
    rw [mul_assoc, hE, mul_ite, mul_zero]
  let Θ : Matrix (Fin n) (Fin n) K →+* R :=
    { toFun := θ
      map_one' := by
        have h : ∀ i j : Fin n, c ((1 : Matrix (Fin n) (Fin n) K) i j) * E i j =
            if i = j then E i j else 0 := by
          intro i j
          rw [Matrix.one_apply]
          split_ifs <;> simp
        rw [hθ]
        simp_rw [h, Finset.sum_ite_eq, Finset.mem_univ, if_true, hE1]
      map_mul' := by
        intro M M'
        rw [hθ, hθ M, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        simp_rw [mul_assoc, hrow M' _ _, Finset.mul_sum, ← mul_assoc, ← map_mul, Matrix.mul_apply,
          map_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
      map_zero' := by rw [hθ]; simp
      map_add' := by
        intro M M'
        rw [hθ, hθ, hθ]
        simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib] }
  have hΘ : ∀ M : Matrix (Fin n) (Fin n) K, Θ M = θ M := fun _ => rfl

  have hextr : ∀ (M : Matrix (Fin n) (Fin n) K) (i j : Fin n),
      ∑ a, E a i * Θ M * E j a = c (M i j) := by
    intro M i j
    simp_rw [hΘ, hrow, Finset.sum_mul, hcol, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_sum, hE1, mul_one]
  have hinj : Function.Injective Θ := by
    intro M M' h
    ext i j
    apply hcinj
    rw [← hextr M i j, ← hextr M' i j, h]
  have hcardM : Nat.card (Matrix (Fin n) (Fin n) K) = Nat.card K ^ (n * n) := by
    show Nat.card (Fin n → Fin n → K) = _
    rw [Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.card_fin]
  have hbij : Function.Bijective Θ :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hcardM])
  exact ⟨(RingEquiv.ofBijective Θ hbij).symm⟩

section stdUnits
variable (K : Type*) [Semiring K]

def e₀ : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]

def u₀ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

def v₀ : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]

theorem e₀_mul_e₀ : e₀ K * e₀ K = e₀ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₀, Matrix.mul_apply, Fin.sum_univ_two]
theorem e₀_mul_u₀ : e₀ K * u₀ K = u₀ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₀, u₀, Matrix.mul_apply, Fin.sum_univ_two]
theorem u₀_mul_e₀ : u₀ K * e₀ K = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₀, u₀, Matrix.mul_apply, Fin.sum_univ_two]
theorem v₀_mul_e₀ : v₀ K * e₀ K = v₀ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₀, v₀, Matrix.mul_apply, Fin.sum_univ_two]
theorem e₀_mul_v₀ : e₀ K * v₀ K = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₀, v₀, Matrix.mul_apply, Fin.sum_univ_two]
theorem u₀_mul_v₀ : u₀ K * v₀ K = e₀ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₀, u₀, v₀, Matrix.mul_apply, Fin.sum_univ_two]
end stdUnits

theorem v₀_mul_u₀ (K : Type*) [Ring K] : v₀ K * u₀ K = 1 - e₀ K := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e₀, u₀, v₀, Matrix.mul_apply, Fin.sum_univ_two]

section order
variable {a b : ℚ}

def orderSubring (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) : Subring ℍ[ℚ, a, b] where
  carrier := Λ
  mul_mem' hx hy := hΛ.mul_mem hx hy
  one_mem' := hΛ.one_mem
  add_mem' hx hy := Λ.add_mem hx hy
  zero_mem' := Λ.zero_mem
  neg_mem' hx := Λ.neg_mem hx

theorem mem_orderSubring {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} :
    x ∈ orderSubring Λ hΛ ↔ x ∈ Λ := Iff.rfl

scoped instance isTwoSided_span_natCast (O : Type*) [Ring O] (N : ℕ) :
    (Ideal.span {(N : O)}).IsTwoSided := by
  refine ⟨fun b ha => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  exact Ideal.mem_span_singleton'.mpr ⟨c * b, by rw [mul_assoc, ← (Nat.cast_commute N b).eq, mul_assoc]⟩

theorem dvd_of_natCast_mem_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} (hN : N ≠ 0)
    {k : ℕ} (hk : ((k : ℕ) : ↥(orderSubring Λ hΛ)) ∈ Ideal.span {(N : ↥(orderSubring Λ hΛ))}) :
    N ∣ k := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hk
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hcH : (c : ℍ[ℚ, a, b]) * (N : ℍ[ℚ, a, b]) = (k : ℍ[ℚ, a, b]) := by
    have h := congrArg Subtype.val hc
    simpa using h
  have hcq : (c : ℍ[ℚ, a, b]) = ((k : ℚ) / N) • (1 : ℍ[ℚ, a, b]) := by
    have hN' : (N : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] (N : ℚ) := (map_natCast _ N).symm
    have hk' : (k : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] (k : ℚ) := (map_natCast _ k).symm
    calc (c : ℍ[ℚ, a, b])
        = (c : ℍ[ℚ, a, b]) * (N : ℍ[ℚ, a, b]) * algebraMap ℚ ℍ[ℚ, a, b] ((N : ℚ)⁻¹) := by
          rw [mul_assoc, hN', ← map_mul, mul_inv_cancel₀ hNq, map_one, mul_one]
      _ = ((k : ℚ) / N) • (1 : ℍ[ℚ, a, b]) := by
          rw [hcH, hk', ← map_mul, Algebra.algebraMap_eq_smul_one, div_eq_mul_inv]
  have hmem : ((k : ℚ) / N) • (1 : ℍ[ℚ, a, b]) ∈ Λ := by
    have h := c.2
    rw [mem_orderSubring, hcq] at h
    exact h
  obtain ⟨m, hm⟩ := (QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hΛ.one_mem).2 _ hmem
  have hkm : (k : ℤ) = m * N := by
    have h' : (m : ℚ) * N = k := by rw [hm, div_mul_cancel₀ _ hNq]
    exact_mod_cast h'.symm
  exact Int.natCast_dvd_natCast.mp ⟨m, by rw [hkm, mul_comm]⟩

theorem natCard_quotient_span_natCast {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ}
    (hN : 0 < N) :
    Nat.card (↥(orderSubring Λ hΛ) ⧸ Ideal.span {(N : ↥(orderSubring Λ hΛ))}) = N ^ 4 := by
  set O := orderSubring Λ hΛ
  set I : Ideal ↥O := Ideal.span {(N : ↥O)} with hI
  rw [← Submodule.cardQuot_apply, Submodule.cardQuot]
  have key := QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hΛ N hN
  rw [AddSubgroup.relIndex] at key
  let f : ↥Λ.toAddSubgroup →+ ↥O :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => ⟨⟨y.1, y.2⟩, rfl⟩
  rw [← (Submodule.toAddSubgroup I).index_comap_of_surjective hf, ← key]
  congr 1
  ext x
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, hI,
    Ideal.mem_span_singleton']
  have hspan : Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (N : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) =
      Λ.map ((N : ℤ) • LinearMap.id) := by
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨y, hy, rfl⟩
  have hNz : ∀ y : ℍ[ℚ, a, b], (N : ℤ) • y = (N : ℍ[ℚ, a, b]) * y := fun y => by
    rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, Algebra.smul_def, map_natCast]
  rw [Submodule.mem_toAddSubgroup, hspan, Submodule.mem_map]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have h := congrArg Subtype.val hc
    simp only [Subring.coe_mul, Subring.coe_natCast] at h
    rw [LinearMap.smul_apply, LinearMap.id_apply, hNz, (Nat.cast_commute N (c : ℍ[ℚ, a, b])).eq, h]
    rfl
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hNz] at hyx
    simp only [Subring.coe_mul, Subring.coe_natCast]
    rw [← (Nat.cast_commute N y).eq, hyx]
    rfl

theorem exists_eq_prod_smul (Λ : Submodule ℤ ℍ[ℚ, a, b]) (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, ℓ.Prime) (x : ℍ[ℚ, a, b]) (hx0 : x ∈ Λ)
    (hx : ∀ ℓ ∈ P, ∃ y ∈ Λ, x = (ℓ : ℚ) • y) :
    ∃ y ∈ Λ, x = ((∏ ℓ ∈ P, ℓ : ℕ) : ℚ) • y := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨x, hx0, by simp⟩
  | insert ℓ P hℓP ih =>
    obtain ⟨y₁, hy₁, hx₁⟩ := hx ℓ (Finset.mem_insert_self ℓ P)
    obtain ⟨y₂, hy₂, hx₂⟩ := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
      (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    set m : ℕ := ∏ i ∈ P, i with hm
    have hcop : Nat.Coprime ℓ m := by
      refine Nat.Coprime.prod_right fun i hi => ?_
      exact (Nat.coprime_primes (hP ℓ (Finset.mem_insert_self ℓ P))
        (hP i (Finset.mem_insert_of_mem hi))).mpr (fun h => hℓP (h ▸ hi))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have huvQ : (u : ℚ) * ℓ + v * m = 1 := by exact_mod_cast huv
    refine ⟨(u : ℚ) • y₂ + (v : ℚ) • y₁, ?_, ?_⟩
    · refine Λ.add_mem ?_ ?_
      · rw [Int.cast_smul_eq_zsmul]; exact Λ.smul_mem u hy₂
      · rw [Int.cast_smul_eq_zsmul]; exact Λ.smul_mem v hy₁
    · rw [Finset.prod_insert hℓP, Nat.cast_mul, ← hm]
      rw [smul_add, smul_smul, smul_smul, show (ℓ : ℚ) * m * u = (ℓ * u) * m by ring,
        show (ℓ : ℚ) * m * v = (m * v) * ℓ by ring, ← smul_smul, ← smul_smul ((m : ℚ) * v),
        ← hx₂, ← hx₁, ← add_smul, show (ℓ : ℚ) * u + m * v = 1 by linear_combination huvQ,
        one_smul]

end order

theorem dvd_prod_primeFactors_pow (N : ℕ) (hN : N ≠ 0) :
    N ∣ (∏ p ∈ N.primeFactors, p) ^ N := by
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ => pow_dvd_pow p (Nat.factorization_lt p hN).le

theorem matrixUnits_table {R : Type*} [Ring R] {e u v : R}
    (hee : e * e = e) (heu : e * u = u) (hue : u * e = 0)
    (hve : v * e = v) (hev : e * v = 0) (huv : u * v = e) (hvu : v * u = 1 - e) :
    (∀ i j k l : Fin 2, ![![e, u], ![v, 1 - e]] i j * ![![e, u], ![v, 1 - e]] k l =
        if j = k then ![![e, u], ![v, 1 - e]] i l else 0) ∧
      ∑ i : Fin 2, ![![e, u], ![v, 1 - e]] i i = 1 := by
  have huu : u * u = 0 := by rw [← heu, mul_assoc, ← mul_assoc u e u, hue, zero_mul, mul_zero]
  have hvv : v * v = 0 := by
    calc v * v = v * e * v := by rw [hve]
      _ = 0 := by rw [mul_assoc, hev, mul_zero]
  have hu1 : u * (1 - e) = u := by rw [mul_sub, mul_one, hue, sub_zero]
  have h1v : (1 - e) * v = v := by rw [sub_mul, one_mul, hev, sub_zero]
  have h1u : (1 - e) * u = 0 := by rw [sub_mul, one_mul, heu, sub_self]
  have hv1 : v * (1 - e) = 0 := by rw [mul_sub, mul_one, hve, sub_self]
  have he1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h1e : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have h11 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h1e, sub_zero]
  refine ⟨fun i j k l => ?_, by simp [Fin.sum_univ_two]⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [hee, heu, hue, hve, hev, huv, hvu, huu, hvv, hu1, h1v, h1u, hv1, he1, h1e, h11]

theorem exists_int_cast_zmod_eq_ite (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (ℓ : ↥P) :
    ∃ r : ℤ, ∀ ℓ' : ↥P, (r : ZMod (ℓ' : ℕ)) = if ℓ = ℓ' then 1 else 0 := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime fun ℓ : ↥P => Ideal.span {((ℓ : ℕ) : ℤ)}) := by
    intro ℓ ℓ' hne
    show IsCoprime (Ideal.span _) (Ideal.span _)
    rw [Ideal.isCoprime_span_singleton_iff, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes (hP ℓ ℓ.2) (hP ℓ' ℓ'.2)).mpr fun h => hne (Subtype.ext h)
  obtain ⟨r, hr⟩ :=
    Ideal.exists_forall_sub_mem_ideal hcop (fun ℓ' => if ℓ = ℓ' then (1 : ℤ) else 0)
  refine ⟨r, fun ℓ' => ?_⟩
  have h := hr ℓ'
  rw [Ideal.mem_span_singleton] at h
  rw [(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp h)]
  split_ifs <;> simp

section reduction
variable {a b : ℚ}

theorem exists_ringHom_matrix_zmod_prime {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ ψ : ↥(orderSubring Λ hΛ.1) →+* Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      Function.Surjective ψ ∧
        ∀ x : ↥(orderSubring Λ hΛ.1), ψ x = 0 ↔
          ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hΛo : IsOrder Λ := hΛ.1
  obtain ⟨φ, h1, hmul, hsurj, hker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  let ψ : ↥(orderSubring Λ hΛ.1) →+* Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    { toFun := fun x => φ ⟨x.1, x.2⟩
      map_one' := h1 hΛo.one_mem
      map_mul' := fun x y => hmul ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ (hΛo.mul_mem x.2 y.2)
      map_zero' := (congrArg φ (Subtype.ext rfl)).trans (map_zero φ)
      map_add' := fun x y =>
        (congrArg φ (Subtype.ext rfl)).trans (map_add φ ⟨x.1, x.2⟩ ⟨y.1, y.2⟩) }
  refine ⟨ψ, fun M => ?_, fun x => hker ⟨x.1, x.2⟩⟩
  obtain ⟨z, hz⟩ := hsurj M
  exact ⟨⟨z.1, z.2⟩, hz⟩

end reduction

section assembly
variable {a b : ℚ}

theorem nonempty_ringEquiv_quotient_matrix_zmod {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    Nonempty ((↥(orderSubring Λ hΛ.1) ⧸ Ideal.span {(N : ↥(orderSubring Λ hΛ.1))}) ≃+*
      Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  classical
  have hΛo : IsOrder Λ := hΛ.1
  have hN0 : N ≠ 0 := NeZero.ne N

  set O : Subring ℍ[ℚ, a, b] := orderSubring Λ hΛo with hOdef
  set I : Ideal ↥O := Ideal.span {(N : ↥O)} with hI

  set P : Finset ℕ := N.primeFactors with hP
  have hprime : ∀ ℓ : ↥P, (ℓ : ℕ).Prime := fun ℓ => Nat.prime_of_mem_primeFactors ℓ.2
  have hdvd : ∀ ℓ : ↥P, (ℓ : ℕ) ∣ N := fun ℓ => Nat.dvd_of_mem_primeFactors ℓ.2

  have key : ∀ ℓ : ↥P, ∃ ψ : ↥O →+* Matrix (Fin 2) (Fin 2) (ZMod (ℓ : ℕ)),
      Function.Surjective ψ ∧
        ∀ x : ↥O, ψ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = ((ℓ : ℕ) : ℚ) • (y : ℍ[ℚ, a, b]) :=
    fun ℓ => exists_ringHom_matrix_zmod_prime hB Λ hΛ (ℓ : ℕ) (hprime ℓ)
      (fun h => hqN (h ▸ hdvd ℓ)) (fun h => hq'N (h ▸ hdvd ℓ))
  choose ψ hψs hψk using key
  let Ψ : ↥O →+* (∀ ℓ : ↥P, Matrix (Fin 2) (Fin 2) (ZMod (ℓ : ℕ))) := RingHom.pi ψ
  have hΨ : ∀ (x : ↥O) (ℓ : ↥P), Ψ x ℓ = ψ ℓ x := fun _ _ => rfl

  have hΨN : ∀ x ∈ I, Ψ x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul]
    suffices h : Ψ (N : ↥O) = 0 by rw [h, mul_zero]
    funext ℓ
    rw [hΨ, Pi.zero_apply, hψk]
    obtain ⟨m, hm⟩ := hdvd ℓ
    refine ⟨⟨((m : ↥O) : ℍ[ℚ, a, b]), (m : ↥O).2⟩, ?_⟩
    simp only [Subring.coe_natCast]
    rw [hm, Nat.cast_mul, Algebra.smul_def, map_natCast]
  let π : (↥O ⧸ I) →+* (∀ ℓ : ↥P, Matrix (Fin 2) (Fin 2) (ZMod (ℓ : ℕ))) :=
    Ideal.Quotient.lift I Ψ hΨN
  have hπ : ∀ x : ↥O, π (Ideal.Quotient.mk I x) = Ψ x := fun x => Ideal.Quotient.lift_mk I Ψ hΨN

  have hδ : ∀ ℓ : ↥P, ∃ r : ℤ, ∀ ℓ' : ↥P, (r : ZMod (ℓ' : ℕ)) = if ℓ = ℓ' then 1 else 0 :=
    exists_int_cast_zmod_eq_ite P (fun ℓ hℓ => Nat.prime_of_mem_primeFactors hℓ)
  choose r hr using hδ
  have hΨsurj : Function.Surjective Ψ := by
    intro s
    choose o ho using fun ℓ => hψs ℓ (s ℓ)
    refine ⟨∑ ℓ, r ℓ • o ℓ, funext fun ℓ' => ?_⟩
    rw [hΨ, map_sum]
    simp_rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (ℓ' : ℕ)), hr, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ho]
  have hπsurj : Function.Surjective π := fun s => by
    obtain ⟨o, ho⟩ := hΨsurj s
    exact ⟨Ideal.Quotient.mk I o, by rw [hπ, ho]⟩

  have hπker : ∀ z ∈ RingHom.ker π, IsNilpotent z := by
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, hπ] at hz
    have hxℓ : ∀ ℓ ∈ P, ∃ y ∈ Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • y := by
      intro ℓ hℓ
      obtain ⟨y, hy⟩ := (hψk ⟨ℓ, hℓ⟩ x).mp (by rw [← hΨ, hz, Pi.zero_apply])
      exact ⟨y, y.2, hy⟩
    obtain ⟨y, hyΛ, hxy⟩ :=
      exists_eq_prod_smul Λ P (fun ℓ hℓ => Nat.prime_of_mem_primeFactors hℓ) x x.2 hxℓ
    have hx' : x = ((∏ ℓ ∈ P, ℓ : ℕ) : ↥O) * ⟨y, hyΛ⟩ := by
      apply Subtype.ext
      show (x : ℍ[ℚ, a, b]) = (((∏ ℓ ∈ P, ℓ : ℕ) : ↥O) : ℍ[ℚ, a, b]) * y
      rw [Subring.coe_natCast, hxy, Algebra.smul_def, map_natCast]
    obtain ⟨m, hm⟩ := dvd_prod_primeFactors_pow N hN0
    refine ⟨N, ?_⟩
    rw [← map_pow, hx', (Nat.cast_commute (∏ ℓ ∈ P, ℓ : ℕ) _).mul_pow, map_mul, ← Nat.cast_pow]
    have h0 : Ideal.Quotient.mk I (((∏ ℓ ∈ P, ℓ) ^ N : ℕ) : ↥O) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.mpr ⟨(m : ↥O), by rw [← Nat.cast_mul, mul_comm, ← hm]⟩
    rw [h0, zero_mul]

  obtain ⟨e', u', v', he', heu, hue, hve, hev, huv, hvu⟩ :=
    exists_matrixUnits_of_surjective_of_ker_isNilpotent π hπsurj hπker
      (e := fun ℓ => e₀ (ZMod (ℓ : ℕ))) (u := fun ℓ => u₀ (ZMod (ℓ : ℕ)))
      (v := fun ℓ => v₀ (ZMod (ℓ : ℕ)))
      (funext fun ℓ => e₀_mul_e₀ _) (funext fun ℓ => e₀_mul_u₀ _) (funext fun ℓ => u₀_mul_e₀ _)
      (funext fun ℓ => v₀_mul_e₀ _) (funext fun ℓ => e₀_mul_v₀ _) (funext fun ℓ => u₀_mul_v₀ _)
      (funext fun ℓ => v₀_mul_u₀ _)

  obtain ⟨hE, hE1⟩ := matrixUnits_table he'.eq heu hue hve hev huv hvu

  haveI hchar : CharP (↥O ⧸ I) N := by
    refine ⟨fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
    · rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem] at hk
      exact dvd_of_natCast_mem_span hΛo hN0 hk
    · obtain ⟨m, rfl⟩ := hk
      have hN' : Ideal.Quotient.mk I (N : ↥O) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [Nat.cast_mul, ← map_natCast (Ideal.Quotient.mk I) N, hN', zero_mul]
  have hcard : Nat.card (↥O ⧸ I) = N ^ 4 :=
    natCard_quotient_span_natCast hΛo (Nat.pos_of_ne_zero hN0)
  haveI : Finite (↥O ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 4 hN0)
  let c : ZMod N →+* (↥O ⧸ I) := ZMod.castHom (dvd_refl N) (↥O ⧸ I)
  have hc : ∀ (k : ZMod N) (x : ↥O ⧸ I), c k * x = x * c k := by
    intro k x
    have hk : c k = ((k.val : ℕ) : ↥O ⧸ I) := by rw [← map_natCast c, ZMod.natCast_zmod_val]
    rw [hk]
    exact (Nat.cast_commute _ _).eq
  have hcinj : Function.Injective c := ZMod.castHom_injective (↥O ⧸ I)
  exact nonempty_ringEquiv_matrix_of_matrixUnits c hc hcinj _ hE hE1
    (by rw [hcard, Nat.card_zmod])

theorem main {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b])) := by
  obtain ⟨ρ⟩ := nonempty_ringEquiv_quotient_matrix_zmod hB Λ hΛ N hqN hq'N
  set O : Subring ℍ[ℚ, a, b] := orderSubring Λ hΛ.1 with hOdef
  set I : Ideal ↥O := Ideal.span {(N : ↥O)} with hI

  let g : ↥Λ →+ ↥O :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let Φ : ↥Λ →+ Matrix (Fin 2) (Fin 2) (ZMod N) :=
    ρ.toRingHom.toAddMonoidHom.comp ((Ideal.Quotient.mk I).toAddMonoidHom.comp g)
  have hΦ : ∀ x : ↥Λ, Φ x = ρ (Ideal.Quotient.mk I ⟨x.1, x.2⟩) := fun _ => rfl
  refine ⟨Φ.toIntLinearMap, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : (⟨(1 : ℍ[ℚ, a, b]), h⟩ : ↥O) = 1 := by
      apply Subtype.ext
      rw [Subring.coe_one]
    rw [AddMonoidHom.coe_toIntLinearMap, hΦ, h1, map_one, map_one]
  · intro x y h
    have hxy : (⟨(x : ℍ[ℚ, a, b]) * y, h⟩ : ↥O) = ⟨x.1, x.2⟩ * ⟨y.1, y.2⟩ := by
      apply Subtype.ext
      rw [Subring.coe_mul]
    rw [AddMonoidHom.coe_toIntLinearMap, hΦ, hΦ, hΦ, hxy, map_mul, map_mul]
  · intro M
    obtain ⟨z, hz⟩ := ρ.surjective M
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨x.1, x.2⟩, by rw [AddMonoidHom.coe_toIntLinearMap, hΦ]; exact hz⟩
  · intro x
    rw [AddMonoidHom.coe_toIntLinearMap, hΦ, EmbeddingLike.map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c', hc'⟩
      refine ⟨⟨c', c'.2⟩, ?_⟩
      have h := congrArg Subtype.val hc'
      simp only [Subring.coe_mul, Subring.coe_natCast] at h
      rw [← h, ← (Nat.cast_commute N _).eq, Algebra.smul_def, map_natCast]
    · rintro ⟨y, hy⟩
      refine ⟨⟨y, y.2⟩, Subtype.ext ?_⟩
      simp only [Subring.coe_mul, Subring.coe_natCast]
      rw [hy, ← (Nat.cast_commute N _).eq, Algebra.smul_def, map_natCast]

end assembly

end KcSplitN
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd.KcSplitN"

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b])) :=
  KcSplitN.main hB Λ hΛ N hqN hq'N

end S_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_not_dvd (solution)
