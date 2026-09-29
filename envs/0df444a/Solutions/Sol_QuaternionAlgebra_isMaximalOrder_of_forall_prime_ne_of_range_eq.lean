-- Prove2me | solution 1 for QuaternionAlgebra.isMaximalOrder_of_forall_prime_ne_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9d85bed0-904e-5623-b1aa-ccce55e3bad5

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_sq_sub_trd_mul_add_nrd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq

set_option autoImplicit false

open scoped Quaternion TensorProduct

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "coe_one lift coe_mul_eq_smul coe_smul exists_natCast_smul_mem_of_mem_span IsMaximalOrder IsOrder sq_sub_trd_mul_add_nrd"
p2m_open "QuaternionAlgebra"

variable {a b : ℚ}

namespace IsOrder p2m_export "QuaternionAlgebra.IsOrder" "mul_mem spanTop exists_intCast_eq_nrd_and_exists_intCast_eq_trd" end IsOrder
namespace IsOrder
p2m_open_scoped "QuaternionAlgebra.IsOrder" in

private theorem _root_.QuaternionAlgebra.IsOrder.exists_int_sq_sub_smul_add_smul_eq_zero {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ) :
    ∃ t n : ℤ, y * y - (t : ℚ) • y + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0 := by
  obtain ⟨⟨n, hn⟩, t, ht⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hy
  refine ⟨t, n, ?_⟩
  have h := QuaternionAlgebra.sq_sub_trd_mul_add_nrd y
  rw [← ht, ← hn] at h
  rw [QuaternionAlgebra.coe_mul_eq_smul] at h
  have h1 : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_one, ← QuaternionAlgebra.coe_smul, smul_eq_mul, mul_one]
  rwa [h1] at h

end IsOrder
p2m_export "QuaternionAlgebra" "IsOrder.exists_int_sq_sub_smul_add_smul_eq_zero"

theorem mem_of_prime_smul_mem_of_pSaturated
    (p : ℕ) [Fact p.Prime] {O : Type*} [Ring O]
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y)
    (θ : O →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hΛ' : IsOrder Λ') {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ') (hpy : (p : ℤ) • y ∈ Λ) :
    y ∈ Λ := by
  obtain ⟨t, n, hrel⟩ := hΛ'.exists_int_sq_sub_smul_add_smul_eq_zero hy

  have hpy' : (p : ℤ) • y ∈ Set.range θ := by rw [hrange]; exact hpy
  obtain ⟨x, hx⟩ := hpy'

  have hxrel : x * x - ((p : ℤ) * t) • x + ((p : ℤ) ^ 2 * n) • (1 : O) = 0 := by
    apply hθ
    rw [map_zero, map_add, map_sub, map_mul, map_zsmul, map_zsmul, map_one, hx]

    have : ((p : ℤ) • y) * ((p : ℤ) • y) - ((p : ℤ) * t) • ((p : ℤ) • y) +
        ((p : ℤ) ^ 2 * n) • (1 : ℍ[ℚ, a, b]) =
        ((p : ℚ) ^ 2) • (y * y - (t : ℚ) • y + (n : ℚ) • (1 : ℍ[ℚ, a, b])) := by
      simp only [← Int.cast_smul_eq_zsmul ℚ, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
        smul_mul_smul_comm]
      module
    rw [this, hrel, smul_zero]
  obtain ⟨x', hx'⟩ := hmaxp x ⟨(p : ℤ) * t, (p : ℤ) ^ 2 * n, hxrel, dvd_mul_right _ _,
    dvd_mul_right _ _⟩

  have hθx' : θ x' = y := by
    have h1 : (p : ℤ) • θ x' = (p : ℤ) • y := by rw [← map_zsmul, ← hx', hx]
    have hp0 : ((p : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have h2 : ((p : ℤ) : ℚ) • θ x' = ((p : ℤ) : ℚ) • y := by
      simpa only [Int.cast_smul_eq_zsmul] using h1
    exact smul_right_injective _ hp0 h2
  rw [← hθx', ← SetLike.mem_coe, ← hrange]
  exact ⟨x', rfl⟩

end QuaternionAlgebra

namespace MaxBodyAux

theorem matrix_eq_zero_of_forall_isNilpotent_mul {F : Type*} [Field F]
    (w : Matrix (Fin 2) (Fin 2) F) (h : ∀ m : Matrix (Fin 2) (Fin 2) F, IsNilpotent (w * m)) :
    w = 0 := by
  have htr : ∀ m : Matrix (Fin 2) (Fin 2) F, Matrix.trace (w * m) = 0 := fun m =>
    (Matrix.isNilpotent_trace_of_isNilpotent (h m)).eq_zero
  ext i j

  have := htr (Matrix.of fun l k => if l = j ∧ k = i then (1 : F) else 0)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
    mul_ite, mul_one, mul_zero] at this
  fin_cases i <;> fin_cases j <;> simpa using this

end MaxBodyAux

namespace MaxBodyAux

open scoped TensorProduct

variable {O : Type*} [Ring O]

noncomputable def redMap (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) :
    O →+* Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
  ((PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).mapMatrix).comp
    ((φ : ℤ_[ℓ] ⊗[ℤ] O →+* Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).comp
      (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] O).toRingHom)

theorem redMap_apply (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) (x : O) :
    redMap ℓ φ x = (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).mapMatrix (φ ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x)) :=
  rfl

theorem mapMatrix_smul (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]) (A : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) :
    (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).mapMatrix (c • A) =
      PadicInt.toZMod c • (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).mapMatrix A := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul]

theorem redMap_surjective (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) :
    Function.Surjective (redMap ℓ φ) := by
  set red : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] →+* Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).mapMatrix with hred

  have key : ∀ t : ℤ_[ℓ] ⊗[ℤ] O, red (φ t) ∈ Set.range (redMap ℓ φ) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [redMap_apply, hred]⟩
    | tmul c o =>
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective (PadicInt.toZMod c)
      refine ⟨k • o, ?_⟩
      have e1 : (c ⊗ₜ[ℤ] o : ℤ_[ℓ] ⊗[ℤ] O) = c • ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] o) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [map_zsmul (redMap ℓ φ), redMap_apply, e1, map_smul, ← hred, mapMatrix_smul, ← hk,
        Int.cast_smul_eq_zsmul]
    | add s t hs ht =>
      obtain ⟨x, hx⟩ := hs
      obtain ⟨y, hy⟩ := ht
      exact ⟨x + y, by rw [map_add, hx, hy, map_add, map_add]⟩
  intro m

  let M : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := m.map (fun z => ((z.val : ℤ) : ℤ_[ℓ]))
  have hM : red M = m := by
    ext i j
    simp [hred, M, Matrix.map_apply]
  obtain ⟨x, hx⟩ := key (φ.symm M)
  exact ⟨x, by rw [hx, AlgEquiv.apply_symm_apply, hM]⟩

end MaxBodyAux

namespace MaxBodyAux

open scoped TensorProduct

variable {O : Type*} [Ring O]

theorem exists_eq_smul_of_redMap_eq_zero (ℓ : ℕ) [Fact ℓ.Prime] [Module.Free ℤ O] [Module.Finite ℤ O]
    (φ : ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) {x : O} (hx : redMap ℓ φ x = 0) :
    ∃ x' : O, x = (ℓ : ℤ) • x' := by
  classical

  have hent : ∀ i j, ∃ c : ℤ_[ℓ], (φ ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x)) i j = (ℓ : ℤ_[ℓ]) * c := by
    intro i j
    have hij := congrFun (congrFun hx i) j
    simp only [redMap_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] at hij
    have hmem : (φ ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x)) i j ∈ RingHom.ker (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ) := hij
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose cM hcM using hent
  set M' : Matrix (Fin 2) (Fin 2) ℤ_[ℓ] := Matrix.of fun i j => cM i j with hM'
  have hφx : φ ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x) = (ℓ : ℤ_[ℓ]) • M' := by
    ext i j; simp [hM', hcM i j, Matrix.smul_apply, smul_eq_mul]

  set t' := φ.symm M' with ht'
  have htx : ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x : ℤ_[ℓ] ⊗[ℤ] O) = (ℓ : ℤ_[ℓ]) • t' := by
    apply φ.injective
    rw [map_smul, ht', AlgEquiv.apply_symm_apply, hφx]

  let B := Module.Free.chooseBasis ℤ O
  let BT := Algebra.TensorProduct.basis ℤ_[ℓ] B
  have hcoord : ∀ i, ((B.repr x i : ℤ) : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) * BT.repr t' i := by
    intro i
    have h1 : BT.repr ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x) i = ((B.repr x i : ℤ) : ℤ_[ℓ]) := by
      simp [BT, Algebra.TensorProduct.basis_repr_tmul]
    rw [← h1, htx, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hdvd : ∀ i, (ℓ : ℤ) ∣ B.repr x i := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ) (hcoord i)
    rw [map_intCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at this
    exact this
  choose q hq using hdvd
  refine ⟨∑ i, q i • B i, ?_⟩
  calc x = ∑ i, B.repr x i • B i := (B.sum_repr x).symm
    _ = ∑ i, ((ℓ : ℤ) * q i) • B i := by simp_rw [← hq]
    _ = (ℓ : ℤ) • ∑ i, q i • B i := by rw [Finset.smul_sum]; simp_rw [mul_smul]

end MaxBodyAux

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "coe_one lift coe_mul_eq_smul coe_smul exists_natCast_smul_mem_of_mem_span IsMaximalOrder IsOrder sq_sub_trd_mul_add_nrd"
p2m_open "QuaternionAlgebra"

open scoped TensorProduct
open MaxBodyAux

variable {a b : ℚ}

theorem mem_of_prime_smul_mem_of_split
    (ℓ : ℕ) [Fact ℓ.Prime] {O : Type*} [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (φ : ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ])
    (θ : O →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hΛ' : IsOrder Λ') (hle : Λ ≤ Λ') {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ') (hℓy : (ℓ : ℤ) • y ∈ Λ) :
    y ∈ Λ := by
  have hℓy' : (ℓ : ℤ) • y ∈ Set.range θ := by rw [hrange]; exact hℓy
  obtain ⟨x, hx⟩ := hℓy'

  have hsq : ∀ o : O, ∃ z : O, (x * o) * (x * o) = (ℓ : ℤ) • z := by
    intro o
    have huΛ : θ o ∈ Λ := by rw [← SetLike.mem_coe, ← hrange]; exact ⟨o, rfl⟩
    have hyu : y * θ o ∈ Λ' := hΛ'.mul_mem hy (hle huΛ)
    obtain ⟨t, n, hrel⟩ := hΛ'.exists_int_sq_sub_smul_add_smul_eq_zero hyu
    refine ⟨t • (x * o) - ((ℓ : ℤ) * n) • (1 : O), hθ ?_⟩
    rw [map_mul, map_mul, map_zsmul, map_sub, map_zsmul, map_zsmul, map_mul, map_one, hx]
    have : ((ℓ : ℤ) • y * θ o) * ((ℓ : ℤ) • y * θ o) -
        (ℓ : ℤ) • (t • ((ℓ : ℤ) • y * θ o) - ((ℓ : ℤ) * n) • (1 : ℍ[ℚ, a, b])) =
        ((ℓ : ℚ) ^ 2) • (y * θ o * (y * θ o) - (t : ℚ) • (y * θ o) + (n : ℚ) • (1 : ℍ[ℚ, a, b])) := by
      simp only [← Int.cast_smul_eq_zsmul ℚ, Int.cast_mul, Int.cast_natCast, smul_mul_assoc,
        smul_mul_smul_comm, mul_smul_comm]
      module
    rw [← sub_eq_zero, this, hrel, smul_zero]

  have hnil : ∀ m : Matrix (Fin 2) (Fin 2) (ZMod ℓ), IsNilpotent (redMap ℓ φ x * m) := by
    intro m
    obtain ⟨o, rfl⟩ := redMap_surjective ℓ φ m
    obtain ⟨z, hz⟩ := hsq o
    refine ⟨2, ?_⟩
    rw [← map_mul, pow_two, ← map_mul, hz, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod ℓ)]
    simp
  have hx0 : redMap ℓ φ x = 0 := matrix_eq_zero_of_forall_isNilpotent_mul _ hnil
  obtain ⟨x', hx'⟩ := exists_eq_smul_of_redMap_eq_zero ℓ φ hx0

  have hθx' : θ x' = y := by
    have h1 : (ℓ : ℤ) • θ x' = (ℓ : ℤ) • y := by rw [← map_zsmul, ← hx', hx]
    have hℓ0 : ((ℓ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have h2 : ((ℓ : ℤ) : ℚ) • θ x' = ((ℓ : ℤ) : ℚ) • y := by
      simpa only [Int.cast_smul_eq_zsmul] using h1
    exact smul_right_injective _ hℓ0 h2
  rw [← hθx', ← SetLike.mem_coe, ← hrange]
  exact ⟨x', rfl⟩

theorem isMaximalOrder_of_forall_prime_ne_of_range_eq_body
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y)
    (θ : O →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    IsMaximalOrder Λ := by
  refine ⟨hΛ, fun Λ' hΛ' hle => le_antisymm (fun y hy => ?_) hle⟩

  have hprime : ∀ q : ℕ, q.Prime → ∀ z ∈ Λ', (q : ℤ) • z ∈ Λ → z ∈ Λ := by
    intro q hq z hz hqz
    haveI : Fact q.Prime := ⟨hq⟩
    by_cases hqp : q = p
    · subst hqp
      exact mem_of_prime_smul_mem_of_pSaturated q hmaxp θ hθ hrange hΛ' hz hqz
    · obtain ⟨φ⟩ := hsplit q hqp
      exact mem_of_prime_smul_mem_of_split q φ θ hθ hrange hΛ' hle hz hqz

  have hyspan : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := by rw [hΛ.spanTop]; trivial
  obtain ⟨n, hn, hny⟩ := exists_natCast_smul_mem_of_mem_span hyspan
  suffices H : ∀ n : ℕ, n ≠ 0 → ∀ z ∈ Λ', ((n : ℕ) : ℤ) • z ∈ Λ → z ∈ Λ from H n hn y hy hny
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn z hz hnz
    rcases Nat.lt_or_ge 1 n with h1n | hn1
    ·
      have hq : n.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hn hm
      have hmlt : m < n := by
        conv_rhs => rw [hm]
        exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hq.one_lt
      have hmz : ((m : ℕ) : ℤ) • z ∈ Λ' := Submodule.smul_mem _ _ hz
      have hqmz : (n.minFac : ℤ) • (((m : ℕ) : ℤ) • z) ∈ Λ := by
        rw [smul_smul, ← Nat.cast_mul, ← hm]; exact hnz
      exact ih m hmlt hm0 z hz (hprime _ hq _ hmz hqmz)
    ·
      have : n = 1 := by omega
      subst this
      simpa using hnz

end QuaternionAlgebra

open IsDedekindDomain NumberField in
theorem solution
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y)
    {a b : ℚ} (θ : O →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    QuaternionAlgebra.IsMaximalOrder Λ :=
  QuaternionAlgebra.isMaximalOrder_of_forall_prime_ne_of_range_eq_body p O hsplit hmaxp θ hθ Λ hΛ hrange

end S_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq
end P2MW
export P2MW.S_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq (solution)
