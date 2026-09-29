-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c4aec4a3-32bb-57be-b3c9-d76838f5bc46

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_BaseChange
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct
open QuaternionAlgebra

universe u v

namespace SplitEngine

theorem map_zsmul_of_map_add {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M → N) (hf : ∀ x y, f (x + y) = f x + f y) (n : ℤ) (x : M) : f (n • x) = n • f x :=
  (AddMonoidHom.mk' f hf).map_zsmul n x

theorem sum_smul_mul_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [Field k]
    {R : Type*} [Ring R] [Algebra k R]
    (e : ι → ι → R) (he : ∀ i j j' l, e i j * e j' l = if j = j' then e i l else 0) (M N : Matrix ι ι k) :
    (∑ i, ∑ j, M i j • e i j) * (∑ i, ∑ j, N i j • e i j) = ∑ i, ∑ j, (M * N) i j • e i j := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  have step : ∀ j' : ι, (∑ j, M i j • e i j) * (∑ l, N j' l • e j' l)
      = ∑ l, (M i j' * N j' l) • e i l := by
    intro j'
    rw [Finset.sum_mul_sum]

    have : ∀ j l, (M i j • e i j) * (N j' l • e j' l) = if j = j' then (M i j * N j' l) • e i l else 0 := by
      intro j l
      rw [smul_mul_smul_comm, he]
      split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_ite_eq' Finset.univ j', if_pos (Finset.mem_univ _)]
  simp_rw [step]

  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]

section CharP

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpq : p ≠ q) (hpq' : p ≠ q')

theorem zsmul_p_eq_zero {R : Type v} [Ring R] [Algebra k R] (r : R) : (p : ℤ) • r = 0 := by
  rw [zsmul_eq_mul, Int.cast_natCast]
  have : ((p : ℕ) : R) = algebraMap k R (p : k) := (map_natCast (algebraMap k R) p).symm
  rw [this, CharP.cast_eq_zero k p, map_zero, zero_mul]

include hB hΛ hpq hpq' in

theorem charP_case :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) k,
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Submodule.span k (Set.range φ) = ⊤ ∧
      ∀ (R : Type v) [Ring R] [Algebra k R] (ρ : ↥Λ →ₗ[ℤ] R),
        (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1) →
        (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x * ρ y) →
        ∃ ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] R, ∀ x : ↥Λ, ψ (φ x) = ρ x := by
  obtain ⟨φp, hφ1, hφmul, hsurj, hker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ p hpq hpq'
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.1.one_mem

  let cst : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  let cM : Matrix (Fin 2) (Fin 2) (ZMod p) →+* Matrix (Fin 2) (Fin 2) k := cst.mapMatrix
  have cM_apply : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod p), cM M = M.map cst := fun M => rfl
  have hadd : ∀ x y : ↥Λ, cM (φp (x + y)) = cM (φp x) + cM (φp y) := fun x y => by
    rw [map_add, map_add]
  refine ⟨⟨⟨fun x => cM (φp x), hadd⟩, fun n x => map_zsmul_of_map_add _ hadd n x⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    show cM (φp ⟨1, h⟩) = 1
    rw [hφ1 h, map_one]
  · intro x y h
    show cM (φp _) = cM (φp x) * cM (φp y)
    rw [hφmul x y h, map_mul]
  ·
    refine eq_top_iff.2 fun M _ => ?_
    rw [Matrix.matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hE : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hE]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨x, hx⟩ := hsurj (Matrix.single i j 1)
    refine ⟨x, ?_⟩
    show cM (φp x) = Matrix.single i j 1
    rw [hx, cM_apply, Matrix.map_single, map_one]
  ·
    intro R _ _ ρ hρ1 hρmul

    have hconst : ∀ x x' : ↥Λ, φp x = φp x' → ρ x = ρ x' := by
      intro x x' hxx'
      have h0 : φp (x - x') = 0 := by rw [map_sub, hxx', sub_self]
      obtain ⟨y, hy⟩ := (hker (x - x')).1 h0
      have hxy : x - x' = (p : ℤ) • y := by
        apply Subtype.ext
        rw [hy, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      have : ρ x - ρ x' = 0 := by
        rw [← map_sub, hxy, map_zsmul_of_map_add ρ (fun u v => map_add ρ u v), zsmul_p_eq_zero k p]
      exact sub_eq_zero.1 this

    let sec : Matrix (Fin 2) (Fin 2) (ZMod p) → ↥Λ := fun m => Classical.choose (hsurj m)
    have hsec : ∀ m, φp (sec m) = m := fun m => Classical.choose_spec (hsurj m)
    let ρb : Matrix (Fin 2) (Fin 2) (ZMod p) → R := fun m => ρ (sec m)
    have hρb : ∀ x : ↥Λ, ρb (φp x) = ρ x := fun x => hconst _ _ (hsec (φp x))
    have hρb_add : ∀ m m', ρb (m + m') = ρb m + ρb m' := by
      intro m m'
      conv_lhs => rw [← hsec m, ← hsec m', ← map_add, hρb]
      rw [map_add]
    have hρb_mul : ∀ m m', ρb (m * m') = ρb m * ρb m' := by
      intro m m'
      have hmem : ((sec m : ↥Λ) : ℍ[ℚ, a, b]) * (sec m' : ℍ[ℚ, a, b]) ∈ Λ := hΛ.1.mul_mem (sec m).2 (sec m').2
      conv_lhs => rw [← hsec m, ← hsec m', ← hφmul _ _ hmem, hρb]
      rw [hρmul _ _ hmem]
    have hρb_one : ρb 1 = 1 := by
      conv_lhs => rw [← hφ1 h1Λ, hρb]
      exact hρ1 h1Λ
    let ρbh : Matrix (Fin 2) (Fin 2) (ZMod p) →+ R := AddMonoidHom.mk' ρb hρb_add
    have hρbh : ∀ m, ρbh m = ρb m := fun m => rfl
    have hρb_smul : ∀ (c : ZMod p) (m : Matrix (Fin 2) (Fin 2) (ZMod p)), ρb (c • m) = (cst c) • ρb m := by
      intro c m
      have hc : c = ((c.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val c).symm
      conv_lhs => rw [hc, Nat.cast_smul_eq_nsmul, ← hρbh, map_nsmul, hρbh]
      rw [show (cst c : k) = (c.val : k) by rw [ZMod.castHom_apply, ZMod.cast_eq_val], Nat.cast_smul_eq_nsmul]

    let E : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod p) := fun i j => Matrix.single i j 1
    let ψl : Matrix (Fin 2) (Fin 2) k →ₗ[k] R :=
      { toFun := fun M => ∑ i, ∑ j, M i j • ρb (E i j)
        map_add' := fun M M' => by
          simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c M => by
          simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
    have hψl : ∀ M : Matrix (Fin 2) (Fin 2) k, ψl M = ∑ i, ∑ j, M i j • ρb (E i j) := fun M => rfl

    have hψl_cast : ∀ m : Matrix (Fin 2) (Fin 2) (ZMod p), ψl (cM m) = ρb m := by
      intro m
      rw [hψl]
      conv_rhs => rw [Matrix.matrix_eq_sum_single m, ← hρbh, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hρbh, cM_apply, Matrix.map_apply]
      have : Matrix.single i j (m i j) = (m i j) • E i j := by
        simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this, hρb_smul]
    have hψl_one : ψl 1 = 1 := by
      rw [← map_one cM, hψl_cast, hρb_one]
    have hE_mul : ∀ i j j' l : Fin 2, ρb (E i j) * ρb (E j' l) = if j = j' then ρb (E i l) else 0 := by
      intro i j j' l
      rw [← hρb_mul]
      split_ifs with hjj
      · subst hjj; simp only [E, Matrix.single_mul_single_same, mul_one]
      · rw [show E i j * E j' l = 0 by simp [E, Matrix.single_mul_single_of_ne, hjj]]
        rw [← hρbh, map_zero]
    have hψl_mul : ∀ M N : Matrix (Fin 2) (Fin 2) k, ψl (M * N) = ψl M * ψl N := by
      intro M N
      rw [hψl, hψl, hψl]
      exact (sum_smul_mul_sum_smul (fun i j => ρb (E i j)) hE_mul M N).symm
    refine ⟨AlgHom.ofLinearMap ψl hψl_one hψl_mul, fun x => ?_⟩
    show ψl (cM (φp x)) = ρ x
    rw [hψl_cast, hρb]

end CharP

end SplitEngine

namespace SplitEngineZero

theorem map_zsmul_of_map_add {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M → N) (hf : ∀ x y, f (x + y) = f x + f y) (n : ℤ) (x : M) : f (n • x) = n • f x :=
  (AddMonoidHom.mk' f hf).map_zsmul n x

section

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')

include hB in

theorem a_ne_zero : a ≠ 0 := by
  intro ha
  let i : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
  have hi : i ≠ 0 := by
    intro h; have := congrArg QuaternionAlgebra.imI h; simp [i] at this
  have hii : i * i = 0 := by
    ext <;> simp [i, ha]
  obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB i hi
  apply hi
  calc i = ↑u⁻¹ * (i * i) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [hii, mul_zero]

include hB in

theorem b_ne_zero : b ≠ 0 := by
  intro hb
  let j : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
  have hj : j ≠ 0 := by
    intro h; have := congrArg QuaternionAlgebra.imJ h; simp [j] at this
  have hjj : j * j = 0 := by
    ext <;> simp [j, hb]
  obtain ⟨u, hu⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB j hj
  apply hj
  calc j = ↑u⁻¹ * (j * j) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [hjj, mul_zero]

end

theorem exists_ne_zero_not_isUnit (k : Type u) [Field k] [IsAlgClosed k] (a b : k) (ha : a ≠ 0) :
    ∃ x : ℍ[k, a, b], x ≠ 0 ∧ ¬ IsUnit x := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self a
  have hs0 : s ≠ 0 := by rintro rfl; exact ha (by simpa using hs)
  let x : ℍ[k, a, b] := ⟨1, s⁻¹, 0, 0⟩
  let y : ℍ[k, a, b] := ⟨1, -s⁻¹, 0, 0⟩
  have hxy : x * y = 0 := by
    ext <;> simp [x, y]
    rw [hs]; field_simp; ring
  have hy : y ≠ 0 := by
    intro h; have := congrArg QuaternionAlgebra.re h; simp [y] at this
  refine ⟨x, ?_, ?_⟩
  · intro h; have := congrArg QuaternionAlgebra.re h; simp [x] at this
  · rintro ⟨u, hu⟩
    apply hy
    calc y = ↑u⁻¹ * (x * y) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hxy, mul_zero]

section CharZero

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

include hB hΛ in

theorem charZero_case :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) k,
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Submodule.span k (Set.range φ) = ⊤ ∧
      ∀ (R : Type v) [Ring R] [Algebra k R] (ρ : ↥Λ →ₗ[ℤ] R),
        (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1) →
        (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x * ρ y) →
        ∃ ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] R, ∀ x : ↥Λ, ψ (φ x) = ρ x := by
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.1.one_mem
  have ha : a ≠ 0 := a_ne_zero hB
  have hb : b ≠ 0 := b_ne_zero hB
  have hak : (a : k) ≠ 0 := by exact_mod_cast ha
  have hbk : (b : k) ≠ 0 := by exact_mod_cast hb

  have h₁ : algebraMap ℚ k a = (a : k) := by simp
  have h₂ : algebraMap ℚ k (0 : ℚ) = (0 : k) := by simp
  have h₃ : algebraMap ℚ k b = (b : k) := by simp
  let jB : ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[k, (a : k), (b : k)] := QuaternionAlgebra.mapOfAlgebraMapEq h₁ h₂ h₃
  have jB_apply : ∀ x : ℍ[ℚ, a, b], jB x = ⟨(x.re : k), (x.imI : k), (x.imJ : k), (x.imK : k)⟩ := fun x => by
    simp [jB, QuaternionAlgebra.mapOfAlgebraMapEq_apply]
  obtain ⟨x₀, hx₀, hx₀u⟩ := exists_ne_zero_not_isUnit k (a : k) (b : k) hak
  obtain ⟨e⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit hak hbk x₀ hx₀ hx₀u

  have hadd : ∀ x y : ↥Λ, e (jB ((x + y : ↥Λ) : ℍ[ℚ, a, b])) = e (jB x) + e (jB y) := fun x y => by
    rw [Submodule.coe_add, map_add, map_add]
  refine ⟨⟨⟨fun x => e (jB x), hadd⟩, fun n x => map_zsmul_of_map_add _ hadd n x⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    show e (jB 1) = 1
    rw [map_one, map_one]
  · intro x y h
    show e (jB ((x : ℍ[ℚ, a, b]) * y)) = e (jB x) * e (jB y)
    rw [map_mul, map_mul]
  ·
    have hspanQ : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤ := hΛ.1.spanTop

    have hmem : ∀ w : ℍ[ℚ, a, b], jB w ∈ Submodule.span k (Set.range fun x : ↥Λ => jB x) := by
      intro w
      have hw : w ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := by rw [hspanQ]; trivial
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [map_smul, ← algebraMap_smul k c (jB x)]
        exact Submodule.smul_mem _ _ hx
    have hspanK : Submodule.span k (Set.range fun x : ↥Λ => jB x) = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      have hz : z = (z.re : k) • jB 1 + (z.imI : k) • jB ⟨0, 1, 0, 0⟩ + (z.imJ : k) • jB ⟨0, 0, 1, 0⟩
          + (z.imK : k) • jB ⟨0, 0, 0, 1⟩ := by
        rw [jB_apply, jB_apply, jB_apply, jB_apply]
        ext <;> simp
      rw [hz]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
        exact Submodule.smul_mem _ _ (hmem _)
    refine eq_top_iff.2 fun M _ => ?_
    have hrange : (Set.range fun x : ↥Λ => e (jB x))
        = ((e : ℍ[k, (a : k), (b : k)] ≃ₐ[k] _).toLinearEquiv : ℍ[k, (a : k), (b : k)] →ₗ[k] _) ''
          Set.range (fun x : ↥Λ => jB x) := by
      ext N
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
      rfl
    have : Submodule.span k (Set.range fun x : ↥Λ => e (jB x)) = ⊤ := by
      rw [hrange, Submodule.span_image, hspanK, Submodule.map_top, LinearMap.range_eq_top]
      exact e.surjective
    have hM : M ∈ Submodule.span k (Set.range fun x : ↥Λ => e (jB x)) := by rw [this]; trivial
    exact hM
  ·
    intro R _ _ ρ hρ1 hρmul

    letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra' fun c x => by
      simp only [RingHom.comp_apply]; exact Algebra.commutes _ _
    haveI : IsScalarTower ℚ k R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

    haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.1.fg
    haveI : IsAddTorsionFree ℍ[ℚ, a, b] := IsAddTorsionFree.of_module_rat _
    haveI : Module.IsTorsionFree ℤ ↥Λ :=
      Function.Injective.moduleIsTorsionFree Λ.subtype Subtype.val_injective (fun _ _ => rfl)
    let bZ := Module.Free.chooseBasis ℤ ↥Λ
    let ι := Module.Free.ChooseBasisIndex ℤ ↥Λ
    have hli : LinearIndependent ℚ (fun i : ι => (bZ i : ℍ[ℚ, a, b])) := by
      have h : LinearIndependent ℤ (fun i : ι => (bZ i : ℍ[ℚ, a, b])) :=
        bZ.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)
      exact (LinearIndependent.iff_fractionRing ℤ ℚ).1 h
    have hsp : ⊤ ≤ Submodule.span ℚ (Set.range fun i : ι => (bZ i : ℍ[ℚ, a, b])) := by
      rw [← hΛ.1.spanTop, Submodule.span_le]
      intro x hx

      have hx' : (⟨x, hx⟩ : ↥Λ) ∈ Submodule.span ℤ (Set.range bZ) := by rw [bZ.span_eq]; trivial
      have : x ∈ Submodule.span ℤ (Set.range fun i : ι => (bZ i : ℍ[ℚ, a, b])) := by
        have himg : (Set.range fun i : ι => (bZ i : ℍ[ℚ, a, b])) = Λ.subtype '' Set.range bZ := by
          ext y; simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]; rfl
        rw [himg, Submodule.span_image]
        exact ⟨⟨x, hx⟩, hx', rfl⟩
      exact Submodule.span_le_restrictScalars ℤ ℚ _ this
    let bQ : Module.Basis ι ℚ ℍ[ℚ, a, b] := Module.Basis.mk hli hsp
    have bQ_apply : ∀ i, bQ i = (bZ i : ℍ[ℚ, a, b]) := fun i => Module.Basis.mk_apply hli hsp i

    let ρQ : ℍ[ℚ, a, b] →ₗ[ℚ] R := bQ.constr ℚ fun i => ρ (bZ i)
    have hρQ_b : ∀ i, ρQ (bZ i : ℍ[ℚ, a, b]) = ρ (bZ i) := fun i => by
      rw [← bQ_apply]; exact bQ.constr_basis ℚ _ i

    have hρQ : ∀ x : ↥Λ, ρQ x = ρ x := by
      intro x
      have hx : x = ∑ i, (bZ.repr x i) • bZ i := (bZ.sum_repr x).symm
      conv_lhs => rw [hx]
      conv_rhs => rw [hx]
      rw [map_sum]
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hρQ_b]
      try exact Int.cast_smul_eq_zsmul ℚ _ _

    have hρQ_mul : ∀ x y : ℍ[ℚ, a, b], ρQ (x * y) = ρQ x * ρQ y := by
      have key : (LinearMap.mul ℚ ℍ[ℚ, a, b]).compr₂ ρQ = (LinearMap.mul ℚ R).compl₁₂ ρQ ρQ := by
        refine bQ.ext fun i => bQ.ext fun j => ?_
        simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', bQ_apply]
        have hmem : ((bZ i : ↥Λ) : ℍ[ℚ, a, b]) * (bZ j : ℍ[ℚ, a, b]) ∈ Λ := hΛ.1.mul_mem (bZ i).2 (bZ j).2
        have := hρQ ⟨_, hmem⟩
        rw [this, hρmul _ _ hmem, ← hρQ, ← hρQ]
      intro x y
      have := LinearMap.congr_fun (LinearMap.congr_fun key x) y
      simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] using this
    have hρQ_one : ρQ 1 = 1 := by
      have := hρQ ⟨1, h1Λ⟩
      rw [Submodule.coe_mk] at this
      rw [this]; exact hρ1 h1Λ
    let ρA : ℍ[ℚ, a, b] →ₐ[ℚ] R := AlgHom.ofLinearMap ρQ hρQ_one hρQ_mul

    let ψ₀ : k ⊗[ℚ] ℍ[ℚ, a, b] →ₐ[k] R :=
      Algebra.TensorProduct.lift (Algebra.ofId k R) ρA (fun s x => Algebra.commute_algebraMap_left s _)
    have hψ₀ : ∀ x : ℍ[ℚ, a, b], ψ₀ ((1 : k) ⊗ₜ[ℚ] x) = ρQ x := fun x => by
      simp only [ψ₀, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    let bc : k ⊗[ℚ] ℍ[ℚ, a, b] ≃ₐ[k] ℍ[k, (a : k), (b : k)] := QuaternionAlgebra.baseChange h₁ h₂ h₃
    have hbc : ∀ x : ℍ[ℚ, a, b], bc ((1 : k) ⊗ₜ[ℚ] x) = jB x := fun x => by
      rw [QuaternionAlgebra.baseChange_tmul, jB_apply]
      ext <;> simp
    refine ⟨ψ₀.comp ((bc.symm : ℍ[k, (a : k), (b : k)] →ₐ[k] _).comp (e.symm : _ →ₐ[k] ℍ[k, (a : k), (b : k)])),
      fun x => ?_⟩
    show ψ₀ (bc.symm (e.symm (e (jB x)))) = ρ x
    rw [e.symm_apply_apply, ← hbc, bc.symm_apply_apply, hψ₀, hρQ]

end CharZero

end SplitEngineZero

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type u) [Field k] [IsAlgClosed k] (hqq' : IsUnit ((q * q' : ℕ) : k)) :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) k,

      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧

      Submodule.span k (Set.range φ) = ⊤ ∧

      ∀ (R : Type v) [Ring R] [Algebra k R] (ρ : ↥Λ →ₗ[ℤ] R),
        (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1) →
        (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x * ρ y) →
        ∃ ψ : Matrix (Fin 2) (Fin 2) k →ₐ[k] R, ∀ x : ↥Λ, ψ (φ x) = ρ x := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    have hqq'0 : ((q * q' : ℕ) : k) ≠ 0 := hqq'.ne_zero
    have hpq : p ≠ q := by
      rintro rfl
      apply hqq'0
      rw [Nat.cast_mul, CharP.cast_eq_zero k p, zero_mul]
    have hpq' : p ≠ q' := by
      rintro rfl
      apply hqq'0
      rw [Nat.cast_mul, CharP.cast_eq_zero k p, mul_zero]
    exact SplitEngine.charP_case.{u, v} hB Λ hΛ k p hpq hpq'
  · subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    exact SplitEngineZero.charZero_case.{u, v} hB Λ hΛ k

end S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed (solution)
