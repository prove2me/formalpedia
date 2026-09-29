-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/93ba3cc2-ed82-5a44-a692-0c7b7e81dbc9

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
import Theorems.Thm_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion

universe u v

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "lift IsMaximalOrder IsOrder IsIndefiniteRamifiedExactlyAt exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne IsMaximalOrder.ne_zero_and_ne_zero IsOrder.casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero"
namespace SeparabilityAux
p2m_open "QuaternionAlgebra"

section Casimir

variable {R : Type v} [Ring R]

def IsCasimir (c : R ⊗[ℤ] R) : Prop :=
  ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)

theorem IsCasimir.zero : IsCasimir (0 : R ⊗[ℤ] R) := fun x => by simp

theorem IsCasimir.add {c c' : R ⊗[ℤ] R} (hc : IsCasimir c) (hc' : IsCasimir c') : IsCasimir (c + c') :=
  fun x => by rw [mul_add, add_mul, hc x, hc' x]

theorem IsCasimir.zsmul {c : R ⊗[ℤ] R} (hc : IsCasimir c) (n : ℤ) : IsCasimir (n • c) :=
  fun x => by rw [mul_smul_comm, smul_mul_assoc, hc x]

theorem IsCasimir.neg {c : R ⊗[ℤ] R} (hc : IsCasimir c) : IsCasimir (-c) := by
  have h := hc.zsmul (-1)
  rwa [neg_one_zsmul] at h

theorem IsCasimir.sub {c c' : R ⊗[ℤ] R} (hc : IsCasimir c) (hc' : IsCasimir c') : IsCasimir (c - c') := by
  rw [sub_eq_add_neg]; exact hc.add hc'.neg

theorem IsCasimir.mul_tmul_one {c : R ⊗[ℤ] R} (hc : IsCasimir c) (z : R) : IsCasimir (c * (z ⊗ₜ[ℤ] (1 : R))) := by
  intro x
  rw [← mul_assoc, hc x, mul_assoc, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one]

theorem IsCasimir.one_tmul_mul {c : R ⊗[ℤ] R} (hc : IsCasimir c) (y : R) : IsCasimir (((1 : R) ⊗ₜ[ℤ] y) * c) := by
  intro x
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_assoc, ← hc x, ← mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem mul'_tmul_one_mul (x : R) (c : R ⊗[ℤ] R) :
    LinearMap.mul' ℤ R ((x ⊗ₜ[ℤ] (1 : R)) * c) = x * LinearMap.mul' ℤ R c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply, one_mul, mul_assoc]
  | add c c' hc hc' => rw [mul_add, map_add, map_add, hc, hc', mul_add]

theorem mul'_mul_one_tmul (x : R) (c : R ⊗[ℤ] R) :
    LinearMap.mul' ℤ R (c * ((1 : R) ⊗ₜ[ℤ] x)) = LinearMap.mul' ℤ R c * x := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply, mul_one, mul_assoc]
  | add c c' hc hc' => rw [add_mul, map_add, map_add, hc, hc', add_mul]

theorem IsCasimir.commute_mul' {c : R ⊗[ℤ] R} (hc : IsCasimir c) (x : R) :
    x * LinearMap.mul' ℤ R c = LinearMap.mul' ℤ R c * x := by
  rw [← mul'_tmul_one_mul, hc x, mul'_mul_one_tmul]

end Casimir

section BaseChange

variable (S : Type u) [CommRing S] (R : Type v) [Ring R]

scoped instance instLeftDistribClass : LeftDistribClass ((S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)) :=
  ⟨fun x y z => Distrib.left_distrib x y z⟩

scoped instance instRightDistribClass : RightDistribClass ((S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)) :=
  ⟨fun x y z => Distrib.right_distrib x y z⟩

noncomputable def iota : R ⊗[ℤ] R →ₐ[ℤ] (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : S ⊗[ℤ] R →ₐ[S] (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)).restrictScalars ℤ).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[ℤ] S ⊗[ℤ] R))
    (((Algebra.TensorProduct.includeRight : S ⊗[ℤ] R →ₐ[S] (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)).restrictScalars ℤ).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[ℤ] S ⊗[ℤ] R))
    (fun x y => by
      show ((1 : S) ⊗ₜ[ℤ] x) ⊗ₜ[S] (1 : S ⊗[ℤ] R) * ((1 : S ⊗[ℤ] R) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] y)) =
        ((1 : S ⊗[ℤ] R) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] y)) * (((1 : S) ⊗ₜ[ℤ] x) ⊗ₜ[S] (1 : S ⊗[ℤ] R))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul,
        mul_one])

variable {S R}

theorem iota_tmul (u v : R) :
    iota S R (u ⊗ₜ[ℤ] v) = ((1 : S) ⊗ₜ[ℤ] u) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] v) := by
  rw [iota, Algebra.TensorProduct.lift_tmul]
  show ((1 : S) ⊗ₜ[ℤ] u) ⊗ₜ[S] (1 : S ⊗[ℤ] R) * ((1 : S ⊗[ℤ] R) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] v)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem mul'_iota (c : R ⊗[ℤ] R) :
    LinearMap.mul' S (S ⊗[ℤ] R) (iota S R c) = (1 : S) ⊗ₜ[ℤ] (LinearMap.mul' ℤ R c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [iota_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add c c' hc hc' => rw [map_add, map_add, map_add, hc, hc', TensorProduct.tmul_add]

theorem map_mulLeft_eq (x : S ⊗[ℤ] R) (e : (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)) :
    TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e = (x ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact (mul_zero (x ⊗ₜ[S] (1 : S ⊗[ℤ] R))).symm
  | tmul u v => rw [TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
  | add c c' hc hc' => rw [map_add, hc, hc', mul_add]

theorem map_mulRight_eq (x : S ⊗[ℤ] R) (e : (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)) :
    TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e = e * ((1 : S ⊗[ℤ] R) ⊗ₜ[S] x) := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact (zero_mul ((1 : S ⊗[ℤ] R) ⊗ₜ[S] x)).symm
  | tmul u v => rw [TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]; rfl
  | add c c' hc hc' => rw [map_add, hc, hc', add_mul]

theorem casimir_iota {c : R ⊗[ℤ] R} (hc : IsCasimir c) (x : S ⊗[ℤ] R) :
    (x ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * iota S R c = iota S R c * ((1 : S ⊗[ℤ] R) ⊗ₜ[S] x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    exact (zero_mul (iota S R c)).trans (mul_zero (iota S R c)).symm
  | tmul s r =>
    have h1 : (s ⊗ₜ[ℤ] r) ⊗ₜ[S] (1 : S ⊗[ℤ] R) = s • ((((1 : S) ⊗ₜ[ℤ] r) ⊗ₜ[S] (1 : S ⊗[ℤ] R))) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (1 : S ⊗[ℤ] R) ⊗ₜ[S] (s ⊗ₜ[ℤ] r) = s • ((1 : S ⊗[ℤ] R) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] r)) := by
      rw [← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : (((1 : S) ⊗ₜ[ℤ] r) ⊗ₜ[S] (1 : S ⊗[ℤ] R)) = iota S R (r ⊗ₜ[ℤ] (1 : R)) := by
      rw [iota_tmul]; rfl
    have h4 : ((1 : S ⊗[ℤ] R) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] r)) = iota S R ((1 : R) ⊗ₜ[ℤ] r) := by
      rw [iota_tmul]; rfl
    rw [h1, h2, smul_mul_assoc, mul_smul_comm, h3, h4, ← map_mul, ← map_mul, hc r]
  | add x x' hx hx' => rw [TensorProduct.add_tmul, TensorProduct.tmul_add, add_mul, mul_add, hx, hx']

theorem exists_separabilityElement_of_casimir {c : R ⊗[ℤ] R} (hc : IsCasimir c) (d : ℤ)
    (hcd : LinearMap.mul' ℤ R c = (d : R)) (hd : IsUnit ((d : ℤ) : S)) :
    ∃ e : (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R),
      LinearMap.mul' S (S ⊗[ℤ] R) e = 1 ∧
      ∀ x : S ⊗[ℤ] R, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
        TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e := by
  obtain ⟨w, hw⟩ := hd
  refine ⟨((w⁻¹ : Sˣ) : S) • iota S R c, ?_, ?_⟩
  · rw [map_smul, mul'_iota, hcd]
    have h1 : ((1 : S) ⊗ₜ[ℤ] ((d : ℤ) : R) : S ⊗[ℤ] R) = ((d : ℤ) : S) • (1 : S ⊗[ℤ] R) := by
      rw [← Algebra.algebraMap_eq_smul_one, map_intCast,
        ← map_intCast (Algebra.TensorProduct.includeRight : R →ₐ[ℤ] S ⊗[ℤ] R) d,
        Algebra.TensorProduct.includeRight_apply]
    rw [h1, ← hw, smul_smul, Units.inv_mul, one_smul]
  · intro x
    rw [map_mulLeft_eq, map_mulRight_eq, mul_smul_comm, smul_mul_assoc, casimir_iota hc x]

end BaseChange

section Units

variable {S : Type u} [CommRing S]

theorem isUnit_natCast_of_forall_prime_dvd {q q' : ℕ} (hu : IsUnit ((q * q' : ℕ) : S)) :
    ∀ n : ℕ, n ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ n → p = q ∨ p = q') → IsUnit ((n : ℕ) : S) := by
  have hq : IsUnit ((q : ℕ) : S) ∧ IsUnit ((q' : ℕ) : S) := by
    rw [Nat.cast_mul] at hu
    exact IsUnit.mul_iff.mp hu
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hp
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · have hmin : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hdvd
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hmlt : m < n := by
        rw [hm]
        exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hmin.one_lt
      have hmu : IsUnit ((m : ℕ) : S) :=
        ih m hmlt hm0 fun p hp' hpm => hp p hp' (hm ▸ Dvd.dvd.mul_left hpm _)
      have hpu : IsUnit ((n.minFac : ℕ) : S) := by
        rcases hp _ hmin ⟨m, hm⟩ with h | h
        · rw [h]; exact hq.1
        · rw [h]; exact hq.2
      rw [hm, Nat.cast_mul]
      exact hpu.mul hmu
    · interval_cases n
      · exact absurd rfl hn
      · simp

theorem isUnit_intCast_of_forall_prime_dvd {q q' : ℕ} (hu : IsUnit ((q * q' : ℕ) : S))
    (d : ℤ) (hd : d ≠ 0) (hp : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p = q ∨ p = q') :
    IsUnit ((d : ℤ) : S) := by
  have hn : IsUnit ((d.natAbs : ℕ) : S) := by
    refine isUnit_natCast_of_forall_prime_dvd hu d.natAbs (Int.natAbs_ne_zero.mpr hd) fun p hp' hpd => hp p hp' ?_
    exact Int.natCast_dvd.mpr hpd
  rcases Int.natAbs_eq d with h | h
  · rw [h, Int.cast_natCast]; exact hn
  · rw [h, Int.cast_neg, Int.cast_natCast]; exact hn.neg

end Units

section Order

open scoped Quaternion
p2m_open "QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit.QuaternionAlgebra"

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

theorem exists_ringHom_matrix_of_prime (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ ψ : R →+* Matrix (Fin 2) (Fin 2) (ZMod ℓ), Function.Surjective ψ ∧
      ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y := by
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  have hmem : ∀ r : R, θ r ∈ Λ := fun r => by
    rw [← SetLike.mem_coe, ← hrange]; exact ⟨r, rfl⟩
  let θΛ : R → ↥Λ := fun r => ⟨θ r, hmem r⟩
  have hθΛ_add : ∀ r s : R, θΛ (r + s) = θΛ r + θΛ s := fun r s => Subtype.ext (map_add θ r s)
  have hone : θΛ 1 = ⟨1, hΛ.isOrder.one_mem⟩ := Subtype.ext (map_one θ)
  let ψ : R →+* Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    { toFun := fun r => φ (θΛ r)
      map_one' := by show φ (θΛ 1) = 1; rw [hone]; exact hφ1 _
      map_mul' := fun r s => by
        have h : θΛ (r * s) = ⟨(θΛ r : ℍ[ℚ, a, b]) * (θΛ s : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (hmem r) (hmem s)⟩ :=
          Subtype.ext (map_mul θ r s)
        show φ (θΛ (r * s)) = φ (θΛ r) * φ (θΛ s)
        rw [h]
        exact hφmul _ _ _
      map_zero' := by
        have h : θΛ 0 = 0 := Subtype.ext (map_zero θ)
        show φ (θΛ 0) = 0
        rw [h, map_zero]
      map_add' := fun r s => by
        show φ (θΛ (r + s)) = φ (θΛ r) + φ (θΛ s)
        rw [hθΛ_add, map_add] }
  refine ⟨ψ, ?_, ?_⟩
  · intro m
    obtain ⟨x, hx⟩ := hφsurj m
    have hxr : (x : ℍ[ℚ, a, b]) ∈ Set.range θ := by rw [hrange]; exact x.2
    obtain ⟨r, hr⟩ := hxr
    refine ⟨r, ?_⟩
    show φ (θΛ r) = m
    have : θΛ r = x := Subtype.ext hr
    rw [this, hx]
  · intro x
    show φ (θΛ x) = 0 ↔ _
    rw [hφker]
    constructor
    · rintro ⟨y, hy⟩
      have hyr : (y : ℍ[ℚ, a, b]) ∈ Set.range θ := by rw [hrange]; exact y.2
      obtain ⟨r, hr⟩ := hyr
      refine ⟨r, hθ ?_⟩
      change θ x = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) at hy
      rw [hy, map_mul, map_natCast, ← hr, Algebra.smul_def, map_natCast]
    · rintro ⟨y, rfl⟩
      refine ⟨θΛ y, ?_⟩
      show θ ((ℓ : R) * y) = (ℓ : ℚ) • θ y
      rw [map_mul, map_natCast, Algebra.smul_def, map_natCast]

theorem free_and_finite_of_range_eq (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    Module.Free ℤ R ∧ Module.Finite ℤ R := by
  have hmem : ∀ r : R, θ r ∈ Λ := fun r => by
    rw [← SetLike.mem_coe, ← hrange]; exact ⟨r, rfl⟩
  let θΛ : R →+ ↥Λ :=
    { toFun := fun r => ⟨θ r, hmem r⟩
      map_zero' := Subtype.ext (map_zero θ)
      map_add' := fun r s => Subtype.ext (map_add θ r s) }
  have hbij : Function.Bijective θΛ := by
    constructor
    · intro r s h
      exact hθ (congrArg Subtype.val h)
    · intro x
      have hxr : (x : ℍ[ℚ, a, b]) ∈ Set.range θ := by rw [hrange]; exact x.2
      obtain ⟨r, hr⟩ := hxr
      exact ⟨r, Subtype.ext hr⟩
  let e : R ≃+ ↥Λ := AddEquiv.ofBijective θΛ hbij
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  haveI : Module.IsTorsionFree ℤ ℍ[ℚ, a, b] := Module.IsTorsionFree.trans ℚ
  haveI : Module.Free ℤ ↥Λ := Module.free_of_finite_type_torsion_free'
  exact ⟨Module.Free.of_equiv e.toIntLinearEquiv.symm, Module.Finite.equiv e.toIntLinearEquiv.symm⟩

theorem exists_casimir_mul'_eq_intCast (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    ∃ (c : R ⊗[ℤ] R) (d : ℤ), IsCasimir c ∧ LinearMap.mul' ℤ R c = (d : R) ∧ d ≠ 0 ∧
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p = q ∨ p = q' := by
  classical
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ
  obtain ⟨hint, c₀, hc₀, hc₀0⟩ :=
    QuaternionAlgebra.IsOrder.casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
      ha hb Λ hΛ.isOrder θ hθ hrange

  let J : Ideal ℤ :=
    { carrier := {n : ℤ | ∃ c : R ⊗[ℤ] R, IsCasimir c ∧ LinearMap.mul' ℤ R c = (n : R)}
      zero_mem' := ⟨0, IsCasimir.zero, by simp⟩
      add_mem' := by
        rintro m n ⟨c, hc, hcm⟩ ⟨c', hc', hcn⟩
        exact ⟨c + c', hc.add hc', by rw [map_add, hcm, hcn, Int.cast_add]⟩
      smul_mem' := by
        rintro m n ⟨c, hc, hcn⟩
        refine ⟨m • c, hc.zsmul m, ?_⟩
        rw [map_zsmul, hcn, smul_eq_mul, Int.cast_mul, zsmul_eq_mul] }
  have hJmem : ∀ {n : ℤ}, n ∈ J ↔ ∃ c : R ⊗[ℤ] R, IsCasimir c ∧ LinearMap.mul' ℤ R c = (n : R) := Iff.rfl
  obtain ⟨n₀, hn₀⟩ := hint c₀ hc₀
  have hn₀J : n₀ ∈ J := ⟨c₀, hc₀, hn₀⟩
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero] at hn₀
    exact hc₀0 hn₀

  let d : ℤ := Submodule.IsPrincipal.generator J
  have hJd : J = Ideal.span {d} := (Submodule.IsPrincipal.span_singleton_generator J).symm
  have hdJ : d ∈ J := Submodule.IsPrincipal.generator_mem J
  obtain ⟨c, hc, hcd⟩ := hJmem.mp hdJ
  have hd0 : d ≠ 0 := by
    intro hd
    have : n₀ ∈ Ideal.span ({d} : Set ℤ) := hJd ▸ hn₀J
    rw [Ideal.mem_span_singleton, hd, zero_dvd_iff] at this
    exact hn₀0 this
  refine ⟨c, d, hc, hcd, hd0, fun p hp hpd => ?_⟩
  by_contra hne
  rw [not_or] at hne
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, hψ, hker⟩ := exists_ringHom_matrix_of_prime hB Λ hΛ θ hθ hrange p hne.1 hne.2
  obtain ⟨hfree, hfin⟩ := free_and_finite_of_range_eq Λ hΛ.isOrder θ hθ hrange
  haveI := hfree
  haveI := hfin
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    exact hc₀0 (map_zero _)
  obtain ⟨c₁, hc₁, hψc₁⟩ :=
    RingHom.exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff p ψ hψ hker c₀ hc₀ hc₀ne
  obtain ⟨n₁, hn₁⟩ := hint c₁ hc₁
  have hn₁J : n₁ ∈ Ideal.span ({d} : Set ℤ) := hJd ▸ (show n₁ ∈ J from ⟨c₁, hc₁, hn₁⟩)
  rw [Ideal.mem_span_singleton] at hn₁J
  have hpn₁ : (p : ℤ) ∣ n₁ := dvd_trans hpd hn₁J
  have h1 : ((n₁ : ℤ) : ZMod p) = 1 := by
    have h := hψc₁
    rw [hn₁, map_intCast] at h
    have h00 := congrFun (congrFun h 0) 0
    simp at h00
    exact h00
  have h0 : ((n₁ : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hpn₁
  rw [h0] at h1
  exact zero_ne_one h1

end Order

end QuaternionAlgebra.SeparabilityAux
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit.QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit.QuaternionAlgebra.SeparabilityAux"
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit.QuaternionAlgebra"

open QuaternionAlgebra.SeparabilityAux in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (S : Type u) [CommRing S] (hqq'u : IsUnit ((q * q' : ℕ) : S)) :
    ∃ e : (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R),
      LinearMap.mul' S (S ⊗[ℤ] R) e = 1 ∧
      ∀ x : S ⊗[ℤ] R, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
        TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e := by
  obtain ⟨c, d, hc, hcd, hd0, hprimes⟩ := exists_casimir_mul'_eq_intCast hB Λ hΛ θ hθ hrange
  exact exists_separabilityElement_of_casimir hc d hcd (isUnit_intCast_of_forall_prime_dvd hqq'u d hd0 hprimes)

end S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_separabilityElement_tensor_of_isIndefiniteRamifiedExactlyAt_of_isUnit (solution)
