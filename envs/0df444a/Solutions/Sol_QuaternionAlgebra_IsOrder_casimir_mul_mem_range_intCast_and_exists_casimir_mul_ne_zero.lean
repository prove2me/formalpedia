-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ec7c8d1d-f399-5563-93b2-5456310e5fdd

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero.QuaternionAlgebra"

universe v

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "algebraMap_eq re imK coe_zero re_mul coe_intCast imJ imI Basis IsOrder trd exists_natCast_smul_mem_of_mem_span commute_iff_exists_eq_smul_one_add_smul IsOrder.exists_int_trd_eq_and_nrd_eq"
namespace OrderCasimirAux
p2m_open "QuaternionAlgebra"

variable {a b : ℚ}

section Casimir

variable {R : Type v} [Ring R]

def IsCasimir (c : R ⊗[ℤ] R) : Prop :=
  ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)

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

theorem torsionFree_of_basis {ι : Type*} (bRR : Module.Basis ι ℤ (R ⊗[ℤ] R)) (m : ℤ) (hm : m ≠ 0)
    (v : R ⊗[ℤ] R) (h : m • v = 0) : v = 0 := by
  apply bRR.ext_elem
  intro i
  have := congrArg (fun w => bRR.repr w i) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact absurd h1 hm
  · simpa using h1

end Casimir

section Setup

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type v} [Ring R] {θ : R →+* ℍ[ℚ, a, b]}

theorem mem_of_range_eq (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (r : R) : θ r ∈ Λ := by
  rw [← SetLike.mem_coe, ← hrange]; exact ⟨r, rfl⟩

theorem exists_eq_of_mem (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ) :
    ∃ r : R, θ r = y := by
  have : y ∈ Set.range θ := by rw [hrange]; exact hy
  exact this

theorem exists_theta_eq_smul (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (h : ℍ[ℚ, a, b]) :
    ∃ (N : ℕ) (r : R), N ≠ 0 ∧ θ r = ((N : ℕ) : ℤ) • h := by
  have hh : h ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := by rw [hΛ.spanTop]; trivial
  obtain ⟨N, hN, hNh⟩ := QuaternionAlgebra.exists_natCast_smul_mem_of_mem_span hh
  obtain ⟨r, hr⟩ := exists_eq_of_mem hrange hNh
  exact ⟨N, r, hN, hr⟩

theorem cancel_natSmul {N : ℕ} (hN : N ≠ 0) {v : ℍ[ℚ, a, b]} (h : ((N : ℕ) : ℤ) • v = 0) : v = 0 := by
  rw [← Int.cast_smul_eq_zsmul ℚ] at h
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast hN)

end Setup

section Centre

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type v} [Ring R] {θ : R →+* ℍ[ℚ, a, b]}

theorem commute_theta_of_central (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (z : R) (hz : ∀ x : R, x * z = z * x) (h : ℍ[ℚ, a, b]) : h * θ z = θ z * h := by
  obtain ⟨N, r, hN, hr⟩ := exists_theta_eq_smul hΛ hrange h
  have h1 : θ r * θ z = θ z * θ r := by rw [← map_mul, ← map_mul, hz r]
  rw [hr, smul_mul_assoc, mul_smul_comm] at h1
  have h2 : ((N : ℕ) : ℤ) • (h * θ z - θ z * h) = 0 := by rw [smul_sub, h1, sub_self]
  exact sub_eq_zero.mp (cancel_natSmul hN h2)

theorem exists_intCast_eq_of_central (ha : a ≠ 0) (hb : b ≠ 0) (hΛ : IsOrder Λ) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (z : R) (hz : ∀ x : R, x * z = z * x) : ∃ n : ℤ, z = (n : R) := by
  set w := θ z with hw
  have hcomm := commute_theta_of_central hΛ hrange z hz

  obtain ⟨c₁, e₁, h₁⟩ := (QuaternionAlgebra.commute_iff_exists_eq_smul_one_add_smul ha hb
    (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) (by simp) w).mp (hcomm _).symm
  obtain ⟨c₂, e₂, h₂⟩ := (QuaternionAlgebra.commute_iff_exists_eq_smul_one_add_smul ha hb
    (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) (by simp) w).mp (hcomm _).symm
  have hI : w.imI = 0 := by rw [h₂]; simp
  have hJ : w.imJ = 0 := by rw [h₁]; simp
  have hK : w.imK = 0 := by rw [h₁]; simp
  have hwre : w = w.re • (1 : ℍ[ℚ, a, b]) := by
    rw [Algebra.smul_def, mul_one]
    ext <;> simp [hI, hJ, hK, QuaternionAlgebra.algebraMap_eq]

  have hwΛ : w.re • (1 : ℍ[ℚ, a, b]) ∈ Λ := by rw [← hwre]; exact mem_of_range_eq hrange z
  obtain ⟨k, hk⟩ := (hΛ.exists_int_trd_eq_and_nrd_eq (mem_of_range_eq hrange z)).2 w.re hwΛ
  refine ⟨k, hθ ?_⟩
  rw [map_intCast, ← hw, hwre, ← hk, Algebra.smul_def, mul_one]
  exact QuaternionAlgebra.coe_intCast k

end Centre

section Trace

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type v} [Ring R] {θ : R →+* ℍ[ℚ, a, b]}

noncomputable def tr (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (x : R) : ℤ :=
  Classical.choose (hΛ.exists_int_trd_eq_and_nrd_eq (mem_of_range_eq hrange x)).1

theorem tr_spec (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (x : R) :
    ((tr hΛ hrange x : ℤ) : ℚ) = trd (θ x) := by
  obtain ⟨n, h1, -⟩ := Classical.choose_spec (hΛ.exists_int_trd_eq_and_nrd_eq (mem_of_range_eq hrange x)).1
  exact h1.symm

theorem trd_eq_two_mul_re (w : ℍ[ℚ, a, b]) : trd w = 2 * w.re := rfl

theorem tr_add (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (x y : R) :
    tr hΛ hrange (x + y) = tr hΛ hrange x + tr hΛ hrange y := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_add, tr_spec, tr_spec, tr_spec, map_add, trd_eq_two_mul_re, trd_eq_two_mul_re, trd_eq_two_mul_re]
  simp [mul_add]

theorem tr_zsmul (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (m : ℤ) (x : R) :
    tr hΛ hrange (m • x) = m * tr hΛ hrange x := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, tr_spec, tr_spec, map_zsmul, trd_eq_two_mul_re, trd_eq_two_mul_re]
  simp [mul_left_comm]

theorem tr_zero (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) : tr hΛ hrange 0 = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [tr_spec, map_zero, trd_eq_two_mul_re]
  simp

theorem tr_sum (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) {ι : Type*} (s : Finset ι)
    (g : ι → R) : tr hΛ hrange (∑ i ∈ s, g i) = ∑ i ∈ s, tr hΛ hrange (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tr_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tr_add, ih]

theorem tr_comm (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (x y : R) :
    tr hΛ hrange (x * y) = tr hΛ hrange (y * x) := by
  apply Int.cast_injective (α := ℚ)
  rw [tr_spec, tr_spec, map_mul, map_mul, trd_eq_two_mul_re, trd_eq_two_mul_re, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.re_mul]
  ring

theorem tr_sum_smul_mul (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) {ι : Type*}
    (s : Finset ι) (z : ι → ℤ) (e : ι → R) (y : R) :
    tr hΛ hrange ((∑ i ∈ s, z i • e i) * y) = ∑ i ∈ s, z i * tr hΛ hrange (e i * y) := by
  rw [Finset.sum_mul, tr_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, tr_zsmul]

theorem tr_mul_sum_smul (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) {ι : Type*}
    (s : Finset ι) (z : ι → ℤ) (e : ι → R) (x : R) :
    tr hΛ hrange (x * ∑ i ∈ s, z i • e i) = ∑ i ∈ s, z i * tr hΛ hrange (x * e i) := by
  rw [Finset.mul_sum, tr_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, tr_zsmul]

theorem eq_zero_of_forall_tr_mul_eq_zero (ha : a ≠ 0) (hb : b ≠ 0) (hΛ : IsOrder Λ) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (y : R) (hy : ∀ x : R, tr hΛ hrange (x * y) = 0) : y = 0 := by
  set w := θ y with hw

  have hre : ∀ h : ℍ[ℚ, a, b], (h * w).re = 0 := by
    intro h
    obtain ⟨N, r, hN, hr⟩ := exists_theta_eq_smul hΛ hrange h
    have h1 : trd (θ (r * y)) = 0 := by rw [← tr_spec hΛ hrange, hy r, Int.cast_zero]
    rw [map_mul, hr, ← hw, smul_mul_assoc, trd_eq_two_mul_re] at h1
    have h2 : (((N : ℕ) : ℤ) • (h * w)).re = ((N : ℕ) : ℤ) * (h * w).re := by simp
    rw [h2] at h1
    have hN' : (((N : ℕ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hN
    have : (2 : ℚ) * (((N : ℕ) : ℤ) : ℚ) ≠ 0 := mul_ne_zero two_ne_zero hN'
    rw [← mul_assoc] at h1
    exact (mul_eq_zero.mp h1).resolve_left this
  have h0 : w.re = 0 := by simpa using hre 1
  have h1 : w.imI = 0 := by
    have := hre ⟨0, 1, 0, 0⟩
    simp only [QuaternionAlgebra.re_mul] at this
    have h' : a * w.imI = 0 := by linarith [this]
    exact (mul_eq_zero.mp h').resolve_left ha
  have h2 : w.imJ = 0 := by
    have := hre ⟨0, 0, 1, 0⟩
    simp only [QuaternionAlgebra.re_mul] at this
    have h' : b * w.imJ = 0 := by linarith [this]
    exact (mul_eq_zero.mp h').resolve_left hb
  have h3 : w.imK = 0 := by
    have := hre ⟨0, 0, 0, 1⟩
    simp only [QuaternionAlgebra.re_mul] at this
    have h' : (a * b) * w.imK = 0 := by linarith [this]
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero ha hb)
  apply hθ
  rw [map_zero, ← hw]
  ext <;> simp [h0, h1, h2, h3]

end Trace

section Gram

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type v} [Ring R] {θ : R →+* ℍ[ℚ, a, b]}
  (hΛ : IsOrder Λ) (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
  {ι : Type*} [Fintype ι] [DecidableEq ι] (bR : Module.Basis ι ℤ R)

noncomputable def gram : Matrix ι ι ℤ := Matrix.of fun i j => tr hΛ hrange (bR i * bR j)

omit [Fintype ι] [DecidableEq ι] in
theorem gram_apply (i j : ι) : gram hΛ hrange bR i j = tr hΛ hrange (bR i * bR j) := rfl

noncomputable def fdual (j : ι) : R := ∑ i, (gram hΛ hrange bR).adjugate i j • bR i

theorem tr_basis_mul_fdual (k j : ι) :
    tr hΛ hrange (bR k * fdual hΛ hrange bR j) = if k = j then (gram hΛ hrange bR).det else 0 := by
  rw [fdual, tr_mul_sum_smul]
  have h : ∑ i, (gram hΛ hrange bR).adjugate i j * tr hΛ hrange (bR k * bR i) =
      (gram hΛ hrange bR * (gram hΛ hrange bR).adjugate) k j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gram_apply, mul_comm]
  rw [h, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem det_smul_eq_sum_left (y : R) :
    (gram hΛ hrange bR).det • y = ∑ k, tr hΛ hrange (y * fdual hΛ hrange bR k) • bR k := by
  apply bR.ext_elem
  intro m
  rw [map_smul, Finsupp.smul_apply, bR.repr_sum_self, smul_eq_mul]
  conv_rhs => rw [← bR.sum_repr y]
  rw [tr_sum_smul_mul]
  have : ∑ i, bR.repr y i * tr hΛ hrange (bR i * fdual hΛ hrange bR m) =
      ∑ i, if i = m then bR.repr y i * (gram hΛ hrange bR).det else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tr_basis_mul_fdual]
    split_ifs <;> simp
  rw [this, Finset.sum_ite_eq' Finset.univ m]
  simp [mul_comm]

theorem det_smul_eq_sum_right (y : R) :
    (gram hΛ hrange bR).det • y = ∑ j, tr hΛ hrange (bR j * y) • fdual hΛ hrange bR j := by
  apply bR.ext_elem
  intro m
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hf : ∀ j, bR.repr (fdual hΛ hrange bR j) m = (gram hΛ hrange bR).adjugate m j := fun j => by
    rw [fdual, bR.repr_sum_self]
  simp only [hf]
  have ht : ∀ j, tr hΛ hrange (bR j * y) = ∑ i, gram hΛ hrange bR j i * bR.repr y i := fun j => by
    conv_lhs => rw [← bR.sum_repr y]
    rw [tr_mul_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gram_apply, mul_comm]
  simp only [ht, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ j, gram hΛ hrange bR j i * bR.repr y i * (gram hΛ hrange bR).adjugate m j =
      ((gram hΛ hrange bR).adjugate * gram hΛ hrange bR) m i * bR.repr y i := fun i => by
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [this, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp [Finset.sum_ite_eq]

noncomputable def cElt : R ⊗[ℤ] R := ∑ j, bR j ⊗ₜ[ℤ] fdual hΛ hrange bR j

theorem tmul_one_mul_cElt (x : R) :
    (x ⊗ₜ[ℤ] (1 : R)) * cElt hΛ hrange bR = ∑ j, (x * bR j) ⊗ₜ[ℤ] fdual hΛ hrange bR j := by
  rw [cElt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem cElt_mul_one_tmul (x : R) :
    cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x) = ∑ k, bR k ⊗ₜ[ℤ] (fdual hΛ hrange bR k * x) := by
  rw [cElt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem det_smul_tmul_one_mul_cElt (x : R) :
    (gram hΛ hrange bR).det • ((x ⊗ₜ[ℤ] (1 : R)) * cElt hΛ hrange bR) =
      ∑ j, ∑ k, tr hΛ hrange (x * bR j * fdual hΛ hrange bR k) • (bR k ⊗ₜ[ℤ] fdual hΛ hrange bR j) := by
  rw [tmul_one_mul_cElt]
  refine (Finset.smul_sum (r := (gram hΛ hrange bR).det) (s := Finset.univ)
    (f := fun j => (x * bR j) ⊗ₜ[ℤ] fdual hΛ hrange bR j)).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (TensorProduct.smul_tmul' (gram hΛ hrange bR).det (x * bR j) (fdual hΛ hrange bR j)).trans ?_
  rw [det_smul_eq_sum_left hΛ hrange bR (x * bR j), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (TensorProduct.smul_tmul' _ _ _).symm

theorem det_smul_cElt_mul_one_tmul (x : R) :
    (gram hΛ hrange bR).det • (cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x)) =
      ∑ k, ∑ j, tr hΛ hrange (bR j * (fdual hΛ hrange bR k * x)) • (bR k ⊗ₜ[ℤ] fdual hΛ hrange bR j) := by
  rw [cElt_mul_one_tmul]
  refine (Finset.smul_sum (r := (gram hΛ hrange bR).det) (s := Finset.univ)
    (f := fun k => bR k ⊗ₜ[ℤ] (fdual hΛ hrange bR k * x))).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (TensorProduct.tmul_smul (gram hΛ hrange bR).det (bR k) (fdual hΛ hrange bR k * x)).symm.trans ?_
  rw [det_smul_eq_sum_right hΛ hrange bR (fdual hΛ hrange bR k * x), TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact TensorProduct.tmul_smul _ _ _

theorem isCasimir_cElt (hD : (gram hΛ hrange bR).det ≠ 0) : IsCasimir (cElt hΛ hrange bR) := by
  intro x
  have h : (gram hΛ hrange bR).det • ((x ⊗ₜ[ℤ] (1 : R)) * cElt hΛ hrange bR) =
      (gram hΛ hrange bR).det • (cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x)) := by
    rw [det_smul_tmul_one_mul_cElt, det_smul_cElt_mul_one_tmul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [mul_assoc, tr_comm hΛ hrange x, mul_assoc]
  have h2 : (gram hΛ hrange bR).det • ((x ⊗ₜ[ℤ] (1 : R)) * cElt hΛ hrange bR - cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x))
      = 0 := by
    have hs := smul_sub (gram hΛ hrange bR).det ((x ⊗ₜ[ℤ] (1 : R)) * cElt hΛ hrange bR)
      (cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x))
    have h' : (gram hΛ hrange bR).det • ((x ⊗ₜ[ℤ] (1 : R)) * cElt hΛ hrange bR) -
        (gram hΛ hrange bR).det • (cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x)) = 0 := by
      have := congrArg (fun w => w - (gram hΛ hrange bR).det • (cElt hΛ hrange bR * ((1 : R) ⊗ₜ[ℤ] x))) h
      simpa only [sub_self] using this
    exact hs.trans h'
  exact sub_eq_zero.mp (torsionFree_of_basis (bR.tensorProduct bR) _ hD _ h2)

theorem mul'_cElt : LinearMap.mul' ℤ R (cElt hΛ hrange bR) = ∑ j, bR j * fdual hΛ hrange bR j := by
  rw [cElt, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.mul'_apply]

theorem tr_mul'_cElt :
    tr hΛ hrange (LinearMap.mul' ℤ R (cElt hΛ hrange bR)) = (Fintype.card ι : ℤ) * (gram hΛ hrange bR).det := by
  rw [mul'_cElt, tr_sum]
  have : ∀ j ∈ (Finset.univ : Finset ι), tr hΛ hrange (bR j * fdual hΛ hrange bR j) = (gram hΛ hrange bR).det :=
    fun j _ => by rw [tr_basis_mul_fdual, if_pos rfl]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Gram

section Det

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type v} [Ring R] {θ : R →+* ℍ[ℚ, a, b]}

theorem det_gram_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (hΛ : IsOrder Λ) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bR : Module.Basis ι ℤ R) : (gram hΛ hrange bR).det ≠ 0 := by
  intro hD
  obtain ⟨v, hv0, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hD
  let y : R := ∑ j, v j • bR j
  have hy : ∀ x : R, tr hΛ hrange (x * y) = 0 := by
    intro x
    conv_lhs => rw [← bR.sum_repr x]
    rw [tr_sum_smul_mul]
    have hin : ∀ i, tr hΛ hrange (bR i * y) = (gram hΛ hrange bR).mulVec v i := fun i => by
      simp only [y]
      rw [tr_mul_sum_smul, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [gram_apply, mul_comm]
    simp only [hin, hGv, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hy0 : y = 0 := eq_zero_of_forall_tr_mul_eq_zero ha hb hΛ hθ hrange y hy
  apply hv0
  have : bR.repr y = 0 := by rw [hy0, map_zero]
  funext j
  have hj := congrArg (fun f => f j) this
  simp only [y, bR.repr_sum_self, Finsupp.coe_zero] at hj
  exact hj

end Det

section Free

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type v} [Ring R] {θ : R →+* ℍ[ℚ, a, b]}

theorem free_and_finite (hΛ : IsOrder Λ) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) : Module.Free ℤ R ∧ Module.Finite ℤ R := by
  let θΛ : R →+ ↥Λ :=
    { toFun := fun r => ⟨θ r, mem_of_range_eq hrange r⟩
      map_zero' := Subtype.ext (map_zero θ)
      map_add' := fun r s => Subtype.ext (map_add θ r s) }
  have hbij : Function.Bijective θΛ := by
    constructor
    · intro r s h
      exact hθ (congrArg Subtype.val h)
    · intro x
      obtain ⟨r, hr⟩ := exists_eq_of_mem hrange x.2
      exact ⟨r, Subtype.ext hr⟩
  let e : R ≃+ ↥Λ := AddEquiv.ofBijective θΛ hbij
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  haveI : Module.IsTorsionFree ℤ ℍ[ℚ, a, b] := Module.IsTorsionFree.trans ℚ
  haveI : Module.Free ℤ ↥Λ := Module.free_of_finite_type_torsion_free'
  exact ⟨Module.Free.of_equiv e.toIntLinearEquiv.symm, Module.Finite.equiv e.toIntLinearEquiv.symm⟩

theorem nontrivial (θ : R →+* ℍ[ℚ, a, b]) : Nontrivial R := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg θ h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

end Free

end QuaternionAlgebra.OrderCasimirAux

open QuaternionAlgebra.OrderCasimirAux in
theorem solution
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    {R : Type v} [Ring R] (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hrange : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) :
    (∀ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) →
        ∃ n : ℤ, LinearMap.mul' ℤ R c = (n : R)) ∧
    ∃ c : R ⊗[ℤ] R, (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)) ∧
      LinearMap.mul' ℤ R c ≠ 0 := by
  classical
  refine ⟨fun c hc => ?_, ?_⟩
  ·
    exact exists_intCast_eq_of_central ha hb hΛ hθ hrange _ fun x => IsCasimir.commute_mul' hc x
  ·
    obtain ⟨hfree, hfin⟩ := free_and_finite hΛ hθ hrange
    haveI := hfree
    haveI := hfin
    haveI : Nontrivial R := nontrivial θ
    haveI : Fintype (Module.Free.ChooseBasisIndex ℤ R) := Module.Free.ChooseBasisIndex.fintype ℤ R
    let bR : Module.Basis (Module.Free.ChooseBasisIndex ℤ R) ℤ R := Module.Free.chooseBasis ℤ R
    haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ R) := bR.index_nonempty
    have hD := det_gram_ne_zero ha hb hΛ hθ hrange bR
    refine ⟨cElt hΛ hrange bR, isCasimir_cElt hΛ hrange bR hD, fun h0 => ?_⟩
    have ht := tr_mul'_cElt hΛ hrange bR
    rw [h0, tr_zero] at ht
    have hcard : (Fintype.card (Module.Free.ChooseBasisIndex ℤ R) : ℤ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_ne_zero hcard hD ht.symm

end S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero (solution)
