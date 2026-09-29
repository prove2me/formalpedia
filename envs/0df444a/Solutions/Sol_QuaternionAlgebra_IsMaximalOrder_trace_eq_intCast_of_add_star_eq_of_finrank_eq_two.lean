-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.trace_eq_intCast_of_add_star_eq_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5c2d6709-715a-5a47-8de7-97fae586b7a7

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

noncomputable section

open scoped Quaternion
p2m_open "QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two.QuaternionAlgebra"

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re_star re lift re_coe coe_sub coe_commutes coe_mul_eq_smul coe_smul coe_intCast IsMaximalOrder IsOrder nrd trd mul_star_eq_coe_nrd IsIndefiniteRamifiedExactlyAt exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd"
namespace IsMaximalOrder
p2m_export "QuaternionAlgebra.IsMaximalOrder" "isOrder"
namespace TraceAwayFromDisc
p2m_open "QuaternionAlgebra.IsMaximalOrder QuaternionAlgebra"

section Factor

variable {Λ₀ : Type*} [AddCommGroup Λ₀] {A : Type*} [Ring A] {E : Type*} [Ring E]

theorem exists_factor (φ : Λ₀ →+ A) (hφ : Function.Surjective φ) (θ : Λ₀ →+ E)
    (hker : ∀ x, φ x = 0 → θ x = 0) :
    ∃ ψ : A →+ E, ∀ x, ψ (φ x) = θ x := by
  have hwd : ∀ x x', φ x = φ x' → θ x = θ x' := by
    intro x x' h
    have h0 : θ (x - x') = 0 := hker _ (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at h0
  refine ⟨AddMonoidHom.mk' (fun y => θ (Function.surjInv hφ y)) ?_, ?_⟩
  · intro y y'
    have hy := Function.surjInv_eq hφ y
    have hy' := Function.surjInv_eq hφ y'
    have hyy' := Function.surjInv_eq hφ (y + y')
    rw [← map_add]
    exact hwd _ _ (by rw [hyy', map_add, hy, hy'])
  · intro x
    exact hwd _ _ (Function.surjInv_eq hφ (φ x))

end Factor

section MatrixUnits

variable {F : Type*} [CommRing F] {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem one_eq_single_add_single :
    (1 : Matrix (Fin 2) (Fin 2) F) = Matrix.single 0 0 1 + Matrix.single 1 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

theorem eq_sum_val_smul_single {ℓ : ℕ} [NeZero ℓ] (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    X = ∑ i : Fin 2, ∑ j : Fin 2, (X i j).val • Matrix.single i j (1 : ZMod ℓ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_single, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

omit [FiniteDimensional k V] in

theorem isProj_range_of_isIdempotentElem (p : Module.End k V) (hp : p * p = p) :
    LinearMap.IsProj (LinearMap.range p) p where
  map_mem x := LinearMap.mem_range_self p x
  map_id x hx := by
    obtain ⟨y, rfl⟩ := hx
    change (p * p) y = p y
    rw [hp]

theorem trace_eq_cast_trace {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (hV : Module.finrank k V = 2)
    (ψ : Matrix (Fin 2) (Fin 2) (ZMod ℓ) →+* Module.End k V) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    LinearMap.trace k V (ψ X) = ZMod.castHom (dvd_refl ℓ) k (Matrix.trace X) := by

  let e : Fin 2 → Fin 2 → Module.End k V := fun i j => ψ (Matrix.single i j 1)
  have he : ∀ i j, e i j = ψ (Matrix.single i j 1) := fun _ _ => rfl
  have hmul_same : ∀ i j l : Fin 2, e i j * e j l = e i l := by
    intro i j l
    rw [he, he, he, ← map_mul, Matrix.single_mul_single_same, mul_one]
  have hmul_ne : ∀ (i j j' l : Fin 2), j ≠ j' → e i j * e j' l = 0 := by
    intro i j j' l h
    rw [he, he, ← map_mul, Matrix.single_mul_single_of_ne (h := h), map_zero]
  have hsum : e 0 0 + e 1 1 = 1 := by
    rw [he, he, ← map_add, ← one_eq_single_add_single, map_one]
  have hp : e 0 0 * e 0 0 = e 0 0 := hmul_same 0 0 0
  have hp' : e 1 1 * e 1 1 = e 1 1 := hmul_same 1 1 1
  have hpp' : e 0 0 * e 1 1 = 0 := hmul_ne 0 0 1 1 (by decide)

  have hker : LinearMap.ker (e 0 0) = LinearMap.range (e 1 1) := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      refine ⟨x, ?_⟩
      have := congrArg (fun f : Module.End k V => f x) hsum
      simp only [LinearMap.add_apply, Module.End.one_apply, hx, zero_add] at this
      exact this
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      change (e 0 0 * e 1 1) y = 0
      rw [hpp', LinearMap.zero_apply]

  have hrank : Module.finrank k (LinearMap.range (e 0 0)) + Module.finrank k (LinearMap.range (e 1 1)) = 2 := by
    rw [← hker, LinearMap.finrank_range_add_finrank_ker, hV]

  have h01 : ∀ y, e 0 1 (e 1 1 y) ∈ LinearMap.range (e 0 0) := by
    intro y
    refine ⟨e 0 1 (e 1 1 y), ?_⟩
    change (e 0 0 * e 0 1) (e 1 1 y) = _
    rw [hmul_same 0 0 1]
  have h10 : ∀ y, e 1 0 (e 0 0 y) ∈ LinearMap.range (e 1 1) := by
    intro y
    refine ⟨e 1 0 (e 0 0 y), ?_⟩
    change (e 1 1 * e 1 0) (e 0 0 y) = _
    rw [hmul_same 1 1 0]
  have hmem01 : ∀ x : V, x ∈ LinearMap.range (e 1 1) → e 0 1 x ∈ LinearMap.range (e 0 0) := by
    rintro x ⟨y, rfl⟩; exact h01 y
  have hmem10 : ∀ x : V, x ∈ LinearMap.range (e 0 0) → e 1 0 x ∈ LinearMap.range (e 1 1) := by
    rintro x ⟨y, rfl⟩; exact h10 y
  let u : LinearMap.range (e 1 1) →ₗ[k] LinearMap.range (e 0 0) :=
    ((e 0 1).domRestrict (LinearMap.range (e 1 1))).codRestrict (LinearMap.range (e 0 0))
      (fun x => hmem01 x.1 x.2)
  let w : LinearMap.range (e 0 0) →ₗ[k] LinearMap.range (e 1 1) :=
    ((e 1 0).domRestrict (LinearMap.range (e 0 0))).codRestrict (LinearMap.range (e 1 1))
      (fun x => hmem10 x.1 x.2)
  have hu : ∀ x : LinearMap.range (e 1 1), (u x : V) = e 0 1 x := fun _ => rfl
  have hw : ∀ x : LinearMap.range (e 0 0), (w x : V) = e 1 0 x := fun _ => rfl
  have hwu : ∀ x : LinearMap.range (e 1 1), w (u x) = x := by
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    rw [hw, hu]
    change (e 1 0 * e 0 1 * e 1 1) y = e 1 1 y
    rw [hmul_same 1 0 1, hp']
  have huw : ∀ x : LinearMap.range (e 0 0), u (w x) = x := by
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    rw [hu, hw]
    change (e 0 1 * e 1 0 * e 0 0) y = e 0 0 y
    rw [hmul_same 0 1 0, hp]
  have hu_inj : Function.Injective u := Function.LeftInverse.injective hwu
  have hw_inj : Function.Injective w := Function.LeftInverse.injective huw
  have h1 : Module.finrank k (LinearMap.range (e 1 1)) ≤ Module.finrank k (LinearMap.range (e 0 0)) :=
    LinearMap.finrank_le_finrank_of_injective hu_inj
  have h2 : Module.finrank k (LinearMap.range (e 0 0)) ≤ Module.finrank k (LinearMap.range (e 1 1)) :=
    LinearMap.finrank_le_finrank_of_injective hw_inj
  have hrp : Module.finrank k (LinearMap.range (e 0 0)) = 1 := by omega
  have hrp' : Module.finrank k (LinearMap.range (e 1 1)) = 1 := by omega

  have htr_p : LinearMap.trace k V (e 0 0) = 1 := by
    rw [(isProj_range_of_isIdempotentElem (e 0 0) hp).trace, hrp, Nat.cast_one]
  have htr_p' : LinearMap.trace k V (e 1 1) = 1 := by
    rw [(isProj_range_of_isIdempotentElem (e 1 1) hp').trace, hrp', Nat.cast_one]
  have htr_01 : LinearMap.trace k V (e 0 1) = 0 := by
    have h : e 0 1 = e 0 1 * e 1 1 := (hmul_same 0 1 1).symm
    rw [h, LinearMap.trace_mul_comm, hmul_ne 1 1 0 1 (by decide), map_zero]
  have htr_10 : LinearMap.trace k V (e 1 0) = 0 := by
    have h : e 1 0 = e 1 0 * e 0 0 := (hmul_same 1 0 0).symm
    rw [h, LinearMap.trace_mul_comm, hmul_ne 0 0 1 0 (by decide), map_zero]

  have hX : ψ X = (X 0 0).val • e 0 0 + (X 0 1).val • e 0 1 + ((X 1 0).val • e 1 0 + (X 1 1).val • e 1 1) := by
    conv_lhs => rw [eq_sum_val_smul_single X]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, map_add, map_add, map_add, map_nsmul, map_nsmul,
      map_nsmul, map_nsmul]
  rw [hX, map_add, map_add, map_add, map_nsmul, map_nsmul, map_nsmul, map_nsmul, htr_p, htr_p', htr_01, htr_10,
    smul_zero, smul_zero, add_zero, zero_add, Matrix.trace_fin_two, map_add, ZMod.castHom_apply,
    ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]

end MatrixUnits

section Arithmetic

variable {a b : ℚ}

theorem sq_eq_trace_smul_sub_det_smul {F : Type*} [CommRing F] (X : Matrix (Fin 2) (Fin 2) F) :
    X * X = Matrix.trace X • X - Matrix.det X • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply] <;> ring

theorem mem_range_scalar_of_smul_eq_smul_one {F : Type*} [Field F] (X : Matrix (Fin 2) (Fin 2) F) {t s : F}
    (ht : t ≠ 0) (h : t • X = s • (1 : Matrix (Fin 2) (Fin 2) F)) : X ∈ Set.range (Matrix.scalar (Fin 2)) := by
  refine ⟨t⁻¹ * s, ?_⟩
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, mul_smul, ← h, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem trace_reduction_eq_intCast
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (m : ↥Λ) (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    Matrix.trace (φ m) = (n : ZMod ℓ) := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.one_mem

  have hnmem : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) = n • (1 : ℍ[ℚ, a, b]) := by
      rw [zsmul_eq_mul, mul_one, QuaternionAlgebra.coe_intCast]
    rw [this]; exact Submodule.smul_mem _ _ h1

  have hstar : star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) - (m : ℍ[ℚ, a, b]) := by
    rw [← hn]; abel
  have hstarmem : star (m : ℍ[ℚ, a, b]) ∈ Λ := by rw [hstar]; exact Submodule.sub_mem _ hnmem m.2

  have hcmem : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem m.2 hstarmem
  set c : ↥Λ := ⟨(m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]), hcmem⟩ with hc_def
  have hc_coe : (c : ℍ[ℚ, a, b]) = ((QuaternionAlgebra.nrd (m : ℍ[ℚ, a, b]) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hc_def, Submodule.coe_mk, QuaternionAlgebra.mul_star_eq_coe_nrd]

  have hcomm : ∀ y : ↥Λ, φ c * φ y = φ y * φ c := by
    intro y
    have hcy : (c : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem c.2 y.2
    have hyc : (y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem y.2 c.2
    rw [← hφmul c y hcy, ← hφmul y c hyc]
    congr 1
    apply Subtype.ext
    change (c : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b])
    rw [hc_coe, QuaternionAlgebra.coe_commutes]
  have hcentral : φ c ∈ Set.range (Matrix.scalar (Fin 2)) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
    obtain ⟨y, hy⟩ := hφsurj (Matrix.single i j 1)
    rw [← hy]
    exact (hcomm y).symm
  obtain ⟨d, hd⟩ := hcentral
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at hd

  have hmm : (m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem m.2 m.2
  have key : (m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) =
      n • (m : ℍ[ℚ, a, b]) - (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) := by
    have e1 : (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) =
        (m : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) - (m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) := by
      rw [hstar, mul_sub]
    have e2 : (m : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]) = n • (m : ℍ[ℚ, a, b]) := by
      rw [← QuaternionAlgebra.coe_commutes, QuaternionAlgebra.coe_mul_eq_smul, Int.cast_smul_eq_zsmul]
    rw [e1, e2, sub_sub_cancel]
  have hmm_eq : (⟨(m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hmm⟩ : ↥Λ) = n • m - c := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul]
    exact key

  set X := φ m with hX_def
  have hXX : X * X = (n : ZMod ℓ) • X - d • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
    rw [hX_def, ← hφmul m m hmm, hmm_eq, map_sub, map_zsmul, ← hd, Int.cast_smul_eq_zsmul]

  have hCH := sq_eq_trace_smul_sub_det_smul X
  have hcomp : (Matrix.trace X - (n : ZMod ℓ)) • X = (Matrix.det X - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
    have h := hXX.symm.trans hCH

    rw [sub_eq_sub_iff_add_eq_add] at h
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (Matrix.det X • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)))]
    exact h.symm
  by_cases hsc : X ∈ Set.range (Matrix.scalar (Fin 2))
  ·
    obtain ⟨e, he⟩ := hsc
    obtain ⟨e', rfl⟩ := ZMod.intCast_surjective e
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at he

    have hx0 : φ (m - e' • ⟨1, h1⟩) = 0 := by
      rw [map_sub, map_zsmul, hφ1 h1, ← hX_def, ← he, Int.cast_smul_eq_zsmul, sub_self]
    obtain ⟨y, hy⟩ := (hφker _).mp hx0

    obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ y.2

    have hre1 : 2 * (m : ℍ[ℚ, a, b]).re = (n : ℚ) := by
      have := congrArg QuaternionAlgebra.re hn
      simp only [QuaternionAlgebra.re_star, mul_zero, add_zero, QuaternionAlgebra.re_coe] at this

      have h2 : ((m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b])).re = (m : ℍ[ℚ, a, b]).re + (m : ℍ[ℚ, a, b]).re := by
        simp
      linarith [h2.symm.trans this]
    have hre2 : (m : ℍ[ℚ, a, b]).re - (e' : ℚ) = (ℓ : ℚ) * (y : ℍ[ℚ, a, b]).re := by
      have := congrArg QuaternionAlgebra.re hy
      have hl : (((m - e' • ⟨1, h1⟩ : ↥Λ)) : ℍ[ℚ, a, b]).re = (m : ℍ[ℚ, a, b]).re - (e' : ℚ) := by
        rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_mk]
        simp
      have hr : (((ℓ : ℚ) • (y : ℍ[ℚ, a, b])) : ℍ[ℚ, a, b]).re = (ℓ : ℚ) * (y : ℍ[ℚ, a, b]).re := by
        simp
      rw [hl, hr] at this
      exact this
    have hre3 : (t : ℚ) = 2 * (y : ℍ[ℚ, a, b]).re := by
      rw [ht]; rfl

    have hnZ : n = 2 * e' + (ℓ : ℤ) * t := by
      have hQ : (n : ℚ) = 2 * (e' : ℚ) + (ℓ : ℚ) * (t : ℚ) := by
        rw [← hre1, hre3]; linarith [hre2]
      exact_mod_cast hQ

    rw [← he, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, hnZ]
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, smul_eq_mul]
    ring
  ·
    by_contra hne
    have ht : Matrix.trace X - (n : ZMod ℓ) ≠ 0 := sub_ne_zero.mpr hne
    exact hsc (mem_range_scalar_of_smul_eq_smul_one X ht hcomp)

end Arithmetic

end QuaternionAlgebra.IsMaximalOrder.TraceAwayFromDisc

end

open scoped Quaternion in
open _root_.QuaternionAlgebra _root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two.QuaternionAlgebra QuaternionAlgebra.IsMaximalOrder.TraceAwayFromDisc in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    {k : Type*} [Field k] [CharP k ℓ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (θ : ↥Λ → Module.End k V)
    (hadd : ∀ x y : ↥Λ, θ (x + y) = θ x + θ y)
    (hone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h⟩ = 1)
    (hmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = θ x * θ y)
    (m : ↥Λ) (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    LinearMap.trace k V (θ m) = (n : k) := by

  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder

  let θ' : ↥Λ →+ Module.End k V := AddMonoidHom.mk' θ hadd
  have hθ' : ∀ x, θ' x = θ x := fun _ => rfl
  have hker : ∀ x : ↥Λ, φ x = 0 → θ' x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := (hφker x).mp hx
    have hxy : x = (ℓ : ℤ) • y := by
      apply Subtype.ext
      rw [hy, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    rw [hxy, map_zsmul]
    ext v
    rw [LinearMap.smul_apply, LinearMap.zero_apply, ← Int.cast_smul_eq_zsmul k, Int.cast_natCast,
      CharP.cast_eq_zero, zero_smul]

  obtain ⟨ψ, hψ⟩ := exists_factor φ.toAddMonoidHom hφsurj θ' hker
  simp only [LinearMap.toAddMonoidHom_coe, hθ'] at hψ

  have hψ1 : ψ 1 = 1 := by rw [← hφ1 hΛo.one_mem, hψ, hone]
  have hψmul : ∀ X Y, ψ (X * Y) = ψ X * ψ Y := by
    intro X Y
    obtain ⟨x, rfl⟩ := hφsurj X
    obtain ⟨y, rfl⟩ := hφsurj Y
    have hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ := hΛo.mul_mem x.2 y.2
    change ψ (φ x * φ y) = ψ (φ x) * ψ (φ y)
    rw [← hφmul x y hxy, hψ, hψ, hψ, hmul x y hxy]
  let ψr : Matrix (Fin 2) (Fin 2) (ZMod ℓ) →+* Module.End k V :=
    { toFun := ψ, map_one' := hψ1, map_mul' := hψmul, map_zero' := map_zero ψ, map_add' := map_add ψ }
  have hψr : ∀ X, ψr X = ψ X := fun _ => rfl

  have htr : LinearMap.trace k V (θ m) = ZMod.castHom (dvd_refl ℓ) k (Matrix.trace (φ m)) := by
    rw [← hψ m, ← hψr, trace_eq_cast_trace hV ψr (φ m)]

  rw [htr, trace_reduction_eq_intCast hΛo φ hφ1 hφmul hφsurj hφker m n hn, map_intCast]

end S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two (solution)
