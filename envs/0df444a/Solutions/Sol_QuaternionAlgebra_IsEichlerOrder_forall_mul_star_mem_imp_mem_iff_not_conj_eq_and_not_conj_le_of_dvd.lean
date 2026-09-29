-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/14f10083-74c8-51e3-9a60-6cc24e40d6db

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise Matrix
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace HeckeLocal

section linalg

variable {F : Type*} [Field F]

theorem mulVec_two (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) (i : Fin 2) :
    (A *ᵥ v) i = A i 0 * v 0 + A i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem vec_ne_zero_iff (v : Fin 2 → F) : v ≠ 0 ↔ v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  constructor
  · intro hv
    by_contra h
    push Not at h
    apply hv
    ext i; fin_cases i <;> simp [h.1, h.2]
  · rintro (h | h) hv <;> exact h (by rw [hv]; rfl)

theorem exists_mulVec_eq (v t : Fin 2 → F) (hv : v ≠ 0) : ∃ X : Matrix (Fin 2) (Fin 2) F, X *ᵥ v = t := by
  rcases (vec_ne_zero_iff v).1 hv with h0 | h1
  · refine ⟨Matrix.of fun i j => if j = 0 then t i * (v 0)⁻¹ else 0, ?_⟩
    ext i
    rw [mulVec_two]
    simp
    field_simp
  · refine ⟨Matrix.of fun i j => if j = 1 then t i * (v 1)⁻¹ else 0, ?_⟩
    ext i
    rw [mulVec_two]
    simp
    field_simp

theorem exists_eq_smul {w u : Fin 2 → F} (hw : w ≠ 0) (h : w 0 * u 1 - w 1 * u 0 = 0) :
    ∃ lam : F, u = lam • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1; apply hw; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨u 1 * (w 1)⁻¹, ?_⟩
    have hu0 : u 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    ext i; fin_cases i
    · simp [h0, hu0]
    · simp; field_simp
  · refine ⟨u 0 * (w 0)⁻¹, ?_⟩
    ext i; fin_cases i
    · simp; field_simp
    · simp; field_simp; linear_combination h

theorem eq_zero_of_mulVec_eq_zero {w u : Fin 2 → F} (h : w 0 * u 1 - w 1 * u 0 ≠ 0)
    {D : Matrix (Fin 2) (Fin 2) F} (hw : D *ᵥ w = 0) (hu : D *ᵥ u = 0) : D = 0 := by
  ext i j
  have e1 : D i 0 * w 0 + D i 1 * w 1 = 0 := by rw [← mulVec_two]; rw [hw]; rfl
  have e2 : D i 0 * u 0 + D i 1 * u 1 = 0 := by rw [← mulVec_two]; rw [hu]; rfl
  fin_cases j
  · have : D i 0 * (w 0 * u 1 - w 1 * u 0) = 0 := by linear_combination u 1 * e1 - w 1 * e2
    simpa using (mul_eq_zero.mp this).resolve_right h
  · have : D i 1 * (w 0 * u 1 - w 1 * u 0) = 0 := by linear_combination (-(u 0)) * e1 + w 0 * e2
    simpa using (mul_eq_zero.mp this).resolve_right h

theorem exists_annihilator (I : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ A : Matrix (Fin 2) (Fin 2) F, A ∈ I ↔ A *ᵥ w = 0 := by
  classical
  obtain ⟨A₀, hA₀I, hA₀⟩ := (Submodule.ne_bot_iff I).1 hI0
  have hdet : A₀.det = 0 := by
    by_contra hdet
    apply hI1
    exact Ideal.eq_top_of_isUnit_mem I hA₀I ((Matrix.isUnit_iff_isUnit_det A₀).2 (isUnit_iff_ne_zero.2 hdet))
  obtain ⟨w, hw, hA₀w⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → F, A₀ *ᵥ u ≠ 0 := by
    by_contra h
    push Not at h
    apply hA₀
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  have hcross : w 0 * u 1 - w 1 * u 0 ≠ 0 := by
    intro hc
    obtain ⟨lam, rfl⟩ := exists_eq_smul hw hc
    apply hu
    rw [Matrix.mulVec_smul, hA₀w, smul_zero]
  refine ⟨w, hw, fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · by_contra hAw
    apply hI1
    obtain ⟨X, hX⟩ := exists_mulVec_eq (A *ᵥ w) w hAw
    obtain ⟨Y, hY⟩ := exists_mulVec_eq (A₀ *ᵥ u) (u - X *ᵥ (A *ᵥ u)) hu
    have h1 : X * A + Y * A₀ = 1 := by
      have hD := eq_zero_of_mulVec_eq_zero hcross (D := X * A + Y * A₀ - 1) ?_ ?_
      · exact sub_eq_zero.mp hD
      · rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hX, hA₀w,
          Matrix.mulVec_zero, Matrix.one_mulVec]
        simp
      · rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hY,
          Matrix.one_mulVec]
        abel
    rw [Ideal.eq_top_iff_one, ← h1]
    exact I.add_mem (Ideal.mul_mem_left I X hA) (Ideal.mul_mem_left I Y hA₀I)
  · obtain ⟨X, hX⟩ := exists_mulVec_eq (A₀ *ᵥ u) (A *ᵥ u) hu
    have hAX : A = X * A₀ := by
      have hD := eq_zero_of_mulVec_eq_zero hcross (D := A - X * A₀) ?_ ?_
      · exact sub_eq_zero.mp hD
      · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hA₀w, hA, Matrix.mulVec_zero, sub_zero]
      · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hX, sub_self]
    rw [hAX]
    exact Ideal.mul_mem_left I X hA₀I

theorem det_one_add_eq_one {N : Matrix (Fin 2) (Fin 2) F} (h : N * N = 0) : (1 + N).det = 1 := by
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
  by_cases ht : N 0 0 + N 1 1 = 0
  · have h11 : N 1 1 = -N 0 0 := by linear_combination ht
    rw [h11]
    linear_combination (-1 : F) * e00
  · have h01 : N 0 1 = 0 := by
      have : N 0 1 * (N 0 0 + N 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right ht
    have h10 : N 1 0 = 0 := by
      have : N 1 0 * (N 0 0 + N 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right ht
    have h00 : N 0 0 = 0 := by
      have : N 0 0 * N 0 0 = 0 := by rw [h01] at e00; linear_combination e00
      exact mul_self_eq_zero.mp this
    have h11 : N 1 1 = 0 := by
      have : N 1 1 * N 1 1 = 0 := by rw [h10] at e11; linear_combination e11
      exact mul_self_eq_zero.mp this
    exact absurd (by rw [h00, h11, add_zero]) ht

theorem mul_self_eq_two' (C : Matrix (Fin 2) (Fin 2) F) :
    C * C = C.trace • C - C.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

end linalg

section lattice

variable {a b : ℚ}

theorem zsmul_eq_ratCast_smul (n : ℤ) (x : ℍ[ℚ, a, b]) : n • x = (n : ℚ) • x :=
  (Int.cast_smul_eq_zsmul ℚ n x).symm

theorem natCast_zsmul_eq_ratCast_smul (n : ℕ) (x : ℍ[ℚ, a, b]) : (n : ℤ) • x = (n : ℚ) • x := by
  rw [zsmul_eq_ratCast_smul]; push_cast; rfl

theorem zsmul_right_cancel {n : ℤ} (hn : n ≠ 0) {x y : ℍ[ℚ, a, b]} (h : n • x = n • y) : x = y := by
  rw [zsmul_eq_ratCast_smul, zsmul_eq_ratCast_smul] at h
  exact smul_right_injective ℍ[ℚ, a, b] (Int.cast_ne_zero.mpr hn) h

def nsub (n : ℕ) (X : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b] :=
  X.map ((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]))

theorem mem_nsub {n : ℕ} {X : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ[ℚ, a, b]} :
    x ∈ nsub n X ↔ ∃ y ∈ X, (n : ℤ) • y = x := by
  simp [nsub, Submodule.mem_map]

theorem nsub_mono {n : ℕ} {X Y : Submodule ℤ ℍ[ℚ, a, b]} (h : X ≤ Y) : nsub n X ≤ nsub n Y :=
  Submodule.map_mono h

theorem span_image_eq_nsub (n : ℕ) (X : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) '' (X : Set ℍ[ℚ, a, b])) = nsub n X := by
  have : (fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) = ⇑((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
    funext y; simp
  rw [this, ← Submodule.map_span, Submodule.span_eq]; rfl

theorem relIndex_nsub_self {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (n : ℕ) (hn : 0 < n) :
    (nsub n X).toAddSubgroup.relIndex X.toAddSubgroup = n ^ 4 := by
  rw [← span_image_eq_nsub]; exact hX.relIndex_span_smul_eq_pow_four n hn

theorem relIndex_nsub_nsub {n : ℕ} (hn : n ≠ 0) (X Y : Submodule ℤ ℍ[ℚ, a, b]) :
    (nsub n X).toAddSubgroup.relIndex (nsub n Y).toAddSubgroup = X.toAddSubgroup.relIndex Y.toAddSubgroup := by
  simp only [nsub, Submodule.map_toAddSubgroup]
  refine AddSubgroup.relIndex_map_map_of_injective _ _ ?_
  intro x y hxy
  have : (n : ℤ) • x = (n : ℤ) • y := by simpa using hxy
  exact zsmul_right_cancel (Int.natCast_ne_zero.mpr hn) this

theorem not_dvd_of_squarefree {N p m : ℕ} (hN : Squarefree N) (hp : p.Prime) (h : N = p * m) : ¬ p ∣ m := by
  rintro ⟨k, rfl⟩
  have : p * p ∣ N := ⟨k, by rw [h]; ring⟩
  exact hp.not_isUnit (hN p this)

theorem mul_self_eq {x : ℍ[ℚ, a, b]} {n t : ℤ} (hn : (n : ℚ) = nrd x) (ht : (t : ℚ) = trd x) :
    x * x = t • x - n • (1 : ℍ[ℚ, a, b]) := by
  have h1 : x * (x + star x) = x * x + ((nrd x : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_add, mul_star_eq_coe_nrd]
  rw [add_star_eq_coe_trd, ← coe_commutes, coe_mul_eq_smul, ← ht, ← hn, Int.cast_smul_eq_zsmul] at h1
  have h3 : (((n : ℤ) : ℚ) : ℍ[ℚ, a, b]) = n • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [h3] at h1
  rw [h1]; abel

theorem cast_eq_one_of_unipotent {p : ℕ} [Fact p.Prime] {g : Matrix (Fin 2) (Fin 2) (ZMod p)} {t n : ℤ}
    (hg2 : (g - 1) * (g - 1) = 0) (hg1 : g ≠ 1) (hch : g * g = (t : ZMod p) • g - (n : ZMod p) • 1) :
    ((n : ℤ) : ZMod p) = 1 := by
  have hsq : g * g = (2 : ZMod p) • g - 1 := by
    have e : (g - 1) * (g - 1) = g * g - (2 : ZMod p) • g + 1 := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, one_mul, two_smul]; abel
    rw [e] at hg2
    rw [← sub_eq_zero, ← hg2]; abel
  have e1 : (t : ZMod p) • g - (n : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = (2 : ZMod p) • g - 1 :=
    hch.symm.trans hsq
  have key : ((t : ZMod p) - 2) • g = ((n : ZMod p) - 1) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [sub_smul, sub_smul, one_smul]
    rw [sub_eq_sub_iff_add_eq_add]
    rw [sub_eq_iff_eq_add] at e1
    rw [e1]; abel
  by_cases ht : (t : ZMod p) - 2 = 0
  · rw [ht, zero_smul] at key
    have h00 := congrFun (congrFun key 0) 0
    simp at h00
    linear_combination (-1 : ZMod p) * h00
  · exfalso
    apply hg1
    set lam : ZMod p := ((t : ZMod p) - 2)⁻¹ * ((n : ZMod p) - 1) with hlam
    have hg : g = lam • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [hlam, mul_smul, ← key, smul_smul, inv_mul_cancel₀ ht, one_smul]
    have h1' : g - 1 = (lam - 1) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by rw [hg, sub_smul, one_smul]
    rw [h1', smul_mul_smul_comm, one_mul] at hg2
    rcases smul_eq_zero.mp hg2 with h | h
    · have : lam = 1 := by rwa [mul_self_eq_zero, sub_eq_zero] at h
      rw [hg, this, one_smul]
    · exact absurd h one_ne_zero

theorem exists_nrd_add_zsmul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x w : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) (hw : w ∈ Λ) (m : ℤ) :
    ∃ j : ℤ, nrd (x + m • w) = nrd x + (m : ℚ) * (j : ℚ) := by
  obtain ⟨n₁, hn₁⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).1
  obtain ⟨n₂, hn₂⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hw).1
  obtain ⟨n₃, hn₃⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd (add_mem hx hw)).1
  refine ⟨n₃ - n₁ - n₂ + m * n₂, ?_⟩
  have key : nrd (x + m • w) = nrd x + (m : ℚ) * (nrd (x + w) - nrd x - nrd w) + (m : ℚ) ^ 2 * nrd w := by
    rw [zsmul_eq_ratCast_smul]
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    obtain ⟨w₀, w₁, w₂, w₃⟩ := w
    simp only [nrd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
    ring
  rw [key, ← hn₁, ← hn₂, ← hn₃]; push_cast; ring

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_smul' (c : ℚ) (x : ℍ[ℚ, a, b]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  ring

theorem star_mem' {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) {x : ℍ[ℚ, a, b]} (hx : x ∈ O) : star x ∈ O := by
  obtain ⟨t, ht⟩ := (hO.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).2
  have e : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [e, ← ht]
  refine sub_mem ?_ hx
  have : (((t : ℤ) : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [this]; exact O.smul_mem t hO.one_mem

theorem not_smul_of_nrd {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) {ℓ : ℕ} (hℓ : ℓ.Prime) {z : ℍ[ℚ, a, b]}
    {n : ℤ} (hz : nrd z = (n : ℚ)) (hn : ¬ ((ℓ : ℤ) ^ 2 ∣ n)) (y : ℍ[ℚ, a, b]) (hy : y ∈ O)
    (h : z = (ℓ : ℚ) • y) : False := by
  obtain ⟨m, hm⟩ := (hO.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hy).1
  apply hn
  refine ⟨m, ?_⟩
  have : (n : ℚ) = ((ℓ : ℤ) ^ 2 * m : ℤ) := by
    rw [← hz, h, nrd_smul', ← hm]; push_cast; ring
  exact_mod_cast this

variable {a b : ℚ}

def lineSub {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ) {N : ℕ}
    (J : Submodule ℤ ℍ[ℚ, a, b]) (h2 : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) (h3 : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ) :
    Submodule (Matrix (Fin 2) (Fin 2) (ZMod p)) (Matrix (Fin 2) (Fin 2) (ZMod p)) where
  carrier := {μ | ∃ y, ∃ hy : y ∈ J, μ = φ ⟨(N : ℤ) • y, h3 y hy⟩}
  zero_mem' := ⟨0, zero_mem _, by
    rw [← map_zero φ]; congr 1; exact Subtype.ext (by simp)⟩
  add_mem' := by
    rintro μ ν ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [← map_add]; congr 1; exact Subtype.ext (by simp [smul_add])
  smul_mem' := by
    rintro X μ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hφsurj X
    have hxy : (x : ℍ[ℚ, a, b]) * y ∈ J := h2 x x.2 y hy
    refine ⟨x * y, hxy, ?_⟩
    have hmem : (x : ℍ[ℚ, a, b]) * ((N : ℤ) • y) ∈ Λ := by rw [mul_smul_comm]; exact h3 _ hxy
    rw [smul_eq_mul, ← hφmul x ⟨(N : ℤ) • y, h3 y hy⟩ hmem]
    congr 1; exact Subtype.ext (mul_smul_comm _ _ _)

theorem mem_lineSub {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ) {N : ℕ}
    (J : Submodule ℤ ℍ[ℚ, a, b]) (h2 : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) (h3 : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ)
    (μ : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    μ ∈ lineSub φ hφmul hφsurj J h2 h3 ↔ ∃ y, ∃ hy : y ∈ J, μ = φ ⟨(N : ℤ) • y, h3 y hy⟩ := Iff.rfl

theorem image_ne_zero_and_ne_one {N : ℕ} (hN0 : N ≠ 0) (hN : Squarefree N)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ)
    (J : Submodule ℤ ℍ[ℚ, a, b]) (h1 : Λ ≤ J) (h2 : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J)
    (h3 : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ) (h4 : Λ.toAddSubgroup.relIndex J.toAddSubgroup = N ^ 2)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (p : ℚ) • (y : ℍ[ℚ, a, b])) :
    (∃ y, ∃ hy : y ∈ J, φ ⟨(N : ℤ) • y, h3 y hy⟩ ≠ 0) ∧ (∀ y (hy : y ∈ J), φ ⟨(N : ℤ) • y, h3 y hy⟩ ≠ 1) := by
  have hpN' := hpN
  obtain ⟨m, hm⟩ := hpN'
  have hpm : ¬ p ∣ m := not_dvd_of_squarefree hN hp hm

  have hNJΛ : nsub N J ≤ Λ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx
    exact h3 y hy
  have hNΛNJ : nsub N Λ ≤ nsub N J := nsub_mono h1
  have hidx1 : (nsub N Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 4 :=
    relIndex_nsub_self hΛo N (Nat.pos_of_ne_zero hN0)
  have hidx2 : (nsub N Λ).toAddSubgroup.relIndex (nsub N J).toAddSubgroup = N ^ 2 := by
    rw [relIndex_nsub_nsub hN0, h4]
  have hidx3 : (nsub N J).toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 2 := by
    have h' := AddSubgroup.relIndex_mul_relIndex (nsub N Λ).toAddSubgroup (nsub N J).toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hNΛNJ hx) (fun x hx => hNJΛ hx)
    rw [hidx1, hidx2, show N ^ 4 = N ^ 2 * N ^ 2 by ring] at h'
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN0) 2) h'
  constructor
  · by_contra hall
    push Not at hall

    have hle : nsub N J ≤ nsub p Λ := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx
      have h0 : φ ⟨(N : ℤ) • y, h3 y hy⟩ = 0 := hall y hy
      obtain ⟨z, hz⟩ := (hφker _).1 h0
      have hz' : (N : ℤ) • y = (p : ℚ) • (z : ℍ[ℚ, a, b]) := hz
      exact mem_nsub.mpr ⟨z, z.2, by rw [natCast_zsmul_eq_ratCast_smul]; exact hz'.symm⟩
    have hidx4 : (nsub p Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = p ^ 4 := relIndex_nsub_self hΛo p hp.pos
    have hchain := AddSubgroup.relIndex_mul_relIndex (nsub N J).toAddSubgroup (nsub p Λ).toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hle hx)
      (fun x hx => by obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx; exact Λ.smul_mem _ hy)
    rw [hidx3, hidx4] at hchain
    have hdvd : p ^ 4 ∣ N ^ 2 := ⟨_, by rw [← hchain, mul_comm]⟩
    rw [hm, mul_pow, show p ^ 4 = p ^ 2 * p ^ 2 by ring] at hdvd
    have hdvd' : p ^ 2 ∣ m ^ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) hdvd
    exact hpm (hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p two_ne_zero) hdvd'))
  · intro y hy hy1

    have hker : φ (⟨(N : ℤ) • y, h3 y hy⟩ - ⟨1, hΛo.one_mem⟩) = 0 := by
      rw [map_sub, hy1, hφ1 hΛo.one_mem, sub_self]
    obtain ⟨z, hz⟩ := (hφker _).1 hker
    have hz' : (N : ℤ) • y - 1 = (p : ℚ) • (z : ℍ[ℚ, a, b]) := hz
    have hz'' : (N : ℚ) • y - 1 = (p : ℚ) • (z : ℍ[ℚ, a, b]) := by
      rw [← natCast_zsmul_eq_ratCast_smul]; exact hz'
    have hone : (1 : ℍ[ℚ, a, b]) = (N : ℚ) • y - (p : ℚ) • (z : ℍ[ℚ, a, b]) := by
      rw [← hz'', sub_sub_cancel]
    have hNq : (N : ℚ) = (p : ℚ) * (m : ℚ) := by exact_mod_cast hm
    have hle : nsub m Λ ≤ nsub N J := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := mem_nsub.mp hx
      have hwy : w * y ∈ J := h2 w hw y hy
      have hwz : w * (z : ℍ[ℚ, a, b]) ∈ Λ := hΛo.mul_mem hw z.2
      refine mem_nsub.mpr ⟨(m : ℤ) • (w * y) - w * z, sub_mem (J.smul_mem _ hwy) (h1 hwz), ?_⟩
      have hw1 : w = (N : ℚ) • (w * y) - (p : ℚ) • (w * (z : ℍ[ℚ, a, b])) := by
        conv_lhs => rw [← mul_one w, hone]
        rw [mul_sub, mul_smul_comm, mul_smul_comm]
      simp only [natCast_zsmul_eq_ratCast_smul]
      rw [hNq] at hw1 ⊢
      conv_rhs => rw [hw1]
      module
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => hN0 (by rw [hm, h, mul_zero]))
    have hidx5 : (nsub m Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = m ^ 4 := relIndex_nsub_self hΛo m hm0
    have hchain := AddSubgroup.relIndex_mul_relIndex (nsub m Λ).toAddSubgroup (nsub N J).toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hle hx) (fun x hx => hNJΛ hx)
    rw [hidx3, hidx5] at hchain
    have hdvd : p ∣ m ^ 4 := by
      rw [← hchain, hm]; exact Dvd.dvd.mul_left (dvd_pow (dvd_mul_right p m) two_ne_zero) _
    exact hpm (hp.dvd_of_dvd_pow hdvd)

end lattice

end HeckeLocal

namespace HeckeLocal
section linalg2
variable {F : Type*} [Field F]

theorem mul_apply_two (A B : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_matrix_col_zero (w : Fin 2 → F) (hw : w ≠ 0) :
    ∃ P Pi : Matrix (Fin 2) (Fin 2) F, P * Pi = 1 ∧ Pi * P = 1 ∧ ∀ i, P i 0 = w i := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      rcases (vec_ne_zero_iff w).1 hw with h | h
      · exact absurd h0 h
      · exact h
    refine ⟨!![0, 1; w 1, 0], !![0, (w 1)⁻¹; 1, 0], ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1]
    · intro i; fin_cases i <;> simp [h0]
  · refine ⟨!![w 0, 0; w 1, 1], !![(w 0)⁻¹, 0; -(w 1 * (w 0)⁻¹), 1], ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0] <;> ring
    · intro i; fin_cases i <;> simp

theorem mulVec_eq_col_zero (P : Matrix (Fin 2) (Fin 2) F) :
    P *ᵥ (Pi.single 0 1) = fun i => P i 0 := by
  ext i; rw [mulVec_two]; simp

theorem conj_apply_zero (Pi B P : Matrix (Fin 2) (Fin 2) F) (w : Fin 2 → F) (hP : ∀ i, P i 0 = w i) (i : Fin 2) :
    (Pi * B * P) i 0 = (Pi *ᵥ (B *ᵥ w)) i := by
  simp only [mul_apply_two, mulVec_two, hP]
  ring

end linalg2
end HeckeLocal

open HeckeLocal in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ))
    (T : (ℍ[ℚ, a, b])ˣ) (hT : (T : ℍ[ℚ, a, b]) = t) :
    (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) ↔
      ((¬ ∀ z : ℍ[ℚ, a, b],
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
        (¬ ∀ r ∈ R,
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ)) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ'
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hRo : IsOrder R := hR.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hℓq : ℓ ≠ q := by rintro rfl; exact hqN hℓN
  have hℓq' : ℓ ≠ q' := by rintro rfl; exact hq'N hℓN
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨M, hM⟩ := hℓN
  have hℓM : ¬ ℓ ∣ M := by
    intro h; obtain ⟨k, hk⟩ := h
    have : ℓ * ℓ ∣ N := ⟨k, by rw [hM, hk, mul_assoc]⟩
    exact hℓ.one_lt.ne' (Nat.isUnit_iff.1 (hN ℓ this))

  set xu : (ℍ[ℚ, a, b])ˣ := w * T * w⁻¹ with hxu
  set x : ℍ[ℚ, a, b] := (xu : ℍ[ℚ, a, b]) with hx
  have hxval : x = (w : ℍ[ℚ, a, b]) * t * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
    rw [hx, hxu, Units.val_mul, Units.val_mul, hT]
  have hxR : x ∈ R := by rw [hxval]; exact (hwnorm t).1 ht
  have hxΛ : x ∈ Λ := hRΛ hxR
  have htΛ : t ∈ Λ := hRΛ ht
  have hwΛ : (w : ℍ[ℚ, a, b]) ∈ Λ := hRΛ hwR
  have hxw : x * (w : ℍ[ℚ, a, b]) = (w : ℍ[ℚ, a, b]) * t := by
    rw [hxval, Units.inv_mul_cancel_right]
  have hnx : nrd x = (ℓ : ℚ) := by
    have h1' : nrd (w : ℍ[ℚ, a, b]) * nrd ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
      rw [← nrd_mul', Units.mul_inv, nrd_one]
    have : nrd x * nrd (w : ℍ[ℚ, a, b]) = nrd (w : ℍ[ℚ, a, b]) * nrd t := by rw [← nrd_mul', hxw, nrd_mul']
    rw [hwn, hnt] at this
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    field_simp at this
    linear_combination this
  have hxbw : star x * (w : ℍ[ℚ, a, b]) = (w : ℍ[ℚ, a, b]) * star t := by
    have e1 : star x * x = ((ℓ : ℚ) : ℍ[ℚ, a, b]) := by rw [star_mul_eq_coe_nrd, hnx]
    have e2 : t * star t = ((ℓ : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_star_eq_coe_nrd, hnt]
    have : (ℓ : ℚ) • (star x * (w : ℍ[ℚ, a, b])) = (ℓ : ℚ) • ((w : ℍ[ℚ, a, b]) * star t) := by
      calc (ℓ : ℚ) • (star x * (w : ℍ[ℚ, a, b])) = star x * (w : ℍ[ℚ, a, b]) * (t * star t) := by
            rw [e2, ← coe_commutes, coe_mul_eq_smul]
        _ = star x * (x * (w : ℍ[ℚ, a, b])) * star t := by rw [hxw]; simp only [mul_assoc]
        _ = (star x * x) * (w : ℍ[ℚ, a, b]) * star t := by simp only [mul_assoc]
        _ = (ℓ : ℚ) • ((w : ℍ[ℚ, a, b]) * star t) := by rw [e1, coe_mul_eq_smul, smul_mul_assoc]
    exact smul_right_injective _ hℓ0 this
  have hstarx : star x = (ℓ : ℚ) • ((xu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
    have h1' : x * star x = ((ℓ : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_star_eq_coe_nrd, hnx]
    calc star x = ((xu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (x * star x) := by rw [hx, Units.inv_mul_cancel_left]
      _ = _ := by rw [h1', ← coe_commutes, coe_mul_eq_smul]

  suffices key : (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) ↔
      ¬ ∀ r ∈ R, ((xu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * x ∈ Λ by
    rw [key]
    constructor
    · intro hS
      exact ⟨fun hnormx => hS fun r hr => hRΛ ((hnormx r).2 hr), hS⟩
    · exact fun h => h.2

  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'
  let Φ : ℍ[ℚ, a, b] → Matrix (Fin 2) (Fin 2) (ZMod ℓ) := fun z => if h : z ∈ Λ then φ ⟨z, h⟩ else 0
  have hΦ : ∀ z (h : z ∈ Λ), Φ z = φ ⟨z, h⟩ := fun z h => dif_pos h
  have Φmul : ∀ {y z : ℍ[ℚ, a, b]}, y ∈ Λ → z ∈ Λ → Φ (y * z) = Φ y * Φ z := by
    intro y z hy hz; rw [hΦ _ (hΛo.mul_mem hy hz), hΦ y hy, hΦ z hz]; exact hφmul ⟨y, hy⟩ ⟨z, hz⟩ _
  have Φone : Φ 1 = 1 := by rw [hΦ 1 hΛo.one_mem]; exact hφ1 _
  have Φadd : ∀ {y z : ℍ[ℚ, a, b]}, y ∈ Λ → z ∈ Λ → Φ (y + z) = Φ y + Φ z := by
    intro y z hy hz; rw [hΦ _ (add_mem hy hz), hΦ y hy, hΦ z hz, ← map_add]; rfl
  have Φzsmul : ∀ (n : ℤ) {y : ℍ[ℚ, a, b]}, y ∈ Λ → Φ (n • y) = n • Φ y := by
    intro n y hy; rw [hΦ _ (Λ.smul_mem n hy), hΦ y hy, ← map_zsmul]; rfl
  have Φker : ∀ {y : ℍ[ℚ, a, b]}, y ∈ Λ → (Φ y = 0 ↔ ∃ z ∈ Λ, y = (ℓ : ℚ) • z) := by
    intro y hy; rw [hΦ y hy, hφker]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z, z.2, hz⟩
    · rintro ⟨z, hzΛ, e⟩; exact ⟨⟨z, hzΛ⟩, e⟩
  have Φnat : ∀ n : ℕ, Φ ((n : ℚ) • (1 : ℍ[ℚ, a, b])) = (n : ZMod ℓ) • 1 := by
    intro n
    rw [← natCast_zsmul_eq_ratCast_smul, Φzsmul _ hΛo.one_mem, Φone,
      ← Int.cast_smul_eq_zsmul (ZMod ℓ) ((n : ℕ) : ℤ) (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ))]
    norm_cast
  have Φℓ : Φ (((ℓ : ℚ) : ℍ[ℚ, a, b])) = 0 := by
    rw [show ((ℓ : ℚ) : ℍ[ℚ, a, b]) = (ℓ : ℚ) • 1 by rw [← coe_mul_eq_smul, mul_one], Φnat]; simp

  have hne : ∀ {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {n : ℤ}, nrd z = (n : ℚ) → ¬ ((ℓ : ℤ) ^ 2 ∣ n) → Φ z ≠ 0 := by
    intro z hz n hzn hn h0
    obtain ⟨y, hy, e⟩ := (Φker hz).1 h0
    exact not_smul_of_nrd hΛo hℓ hzn hn y hy e
  have hℓsq : ¬ ((ℓ : ℤ) ^ 2 ∣ (ℓ : ℤ)) := by
    intro h
    have : (ℓ : ℤ) ^ 2 ≤ ℓ := Int.le_of_dvd (by exact_mod_cast hℓ.pos) h
    have h2 : (2 : ℤ) ≤ ℓ := by exact_mod_cast hℓ.two_le
    nlinarith
  have hℓsqN : ¬ ((ℓ : ℤ) ^ 2 ∣ (N : ℤ)) := by
    intro h
    have : ℓ * ℓ ∣ N := by rw [← sq]; exact_mod_cast h
    exact hℓ.one_lt.ne' (Nat.isUnit_iff.1 (hN ℓ this))
  have nrd_star' : ∀ z : ℍ[ℚ, a, b], nrd (star z) = nrd z := by
    intro z; obtain ⟨z₀, z₁, z₂, z₃⟩ := z; simp [nrd, QuaternionAlgebra.star_mk]

  let I := lineSub φ hφmul hφsurj J' h2 h3 (N := N)
  have hImem : ∀ μ, μ ∈ I ↔ ∃ y ∈ J', μ = Φ ((N : ℤ) • y) := by
    intro μ; rw [mem_lineSub]
    constructor
    · rintro ⟨y, hy, e⟩; exact ⟨y, hy, by rw [e, hΦ]⟩
    · rintro ⟨y, hy, e⟩; exact ⟨y, hy, by rw [e, hΦ _ (h3 y hy)]⟩
  obtain ⟨⟨y₀, hy₀, hy₀ne⟩, hnot1⟩ := image_ne_zero_and_ne_one hN0 hN hΛo J' h1 h2 h3 h4 hℓ ⟨M, hM⟩ φ hφ1 hφker
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hy₀ne
    have : φ ⟨(N : ℤ) • y₀, h3 y₀ hy₀⟩ ∈ I := (mem_lineSub _ _ _ _ _ _ _).2 ⟨y₀, hy₀, rfl⟩
    rw [h] at this; exact (Submodule.mem_bot _).1 this
  have hI1 : I ≠ ⊤ := by
    intro h
    have : (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ∈ I := by rw [h]; exact Submodule.mem_top
    obtain ⟨y, hy, e⟩ := (mem_lineSub _ _ _ _ _ _ _).1 this
    exact hnot1 y hy e.symm
  obtain ⟨w₀, hw₀, hann⟩ := exists_annihilator I hI0 hI1

  obtain ⟨P, Pinv, hPPi, hPiP, hPcol⟩ := exists_matrix_col_zero w₀ hw₀
  let ψ : ℍ[ℚ, a, b] → Matrix (Fin 2) (Fin 2) (ZMod ℓ) := fun z => Pinv * Φ z * P
  have hψ : ∀ z, ψ z = Pinv * Φ z * P := fun z => rfl
  have ψmul : ∀ {y z : ℍ[ℚ, a, b]}, y ∈ Λ → z ∈ Λ → ψ (y * z) = ψ y * ψ z := by
    intro y z hy hz
    simp only [hψ, Φmul hy hz]
    rw [show Pinv * Φ y * P * (Pinv * Φ z * P) = Pinv * (Φ y * (P * Pinv) * Φ z) * P by simp only [mul_assoc],
      hPPi, mul_one]
  have ψadd : ∀ {y z : ℍ[ℚ, a, b]}, y ∈ Λ → z ∈ Λ → ψ (y + z) = ψ y + ψ z := by
    intro y z hy hz; rw [hψ, Φadd hy hz, mul_add, add_mul]
  have ψzsmul : ∀ (n : ℤ) {y : ℍ[ℚ, a, b]}, y ∈ Λ → ψ (n • y) = n • ψ y := by
    intro n y hy; rw [hψ, Φzsmul n hy, Matrix.mul_smul, Matrix.smul_mul]
  have ψzero_iff : ∀ {y : ℍ[ℚ, a, b]}, y ∈ Λ → (ψ y = 0 ↔ ∃ z ∈ Λ, y = (ℓ : ℚ) • z) := by
    intro y hy
    rw [← Φker hy, hψ]
    constructor
    · intro h
      have : P * (Pinv * Φ y * P) * Pinv = 0 := by rw [h, mul_zero, zero_mul]
      rwa [show P * (Pinv * Φ y * P) * Pinv = (P * Pinv) * Φ y * (P * Pinv) by simp only [mul_assoc], hPPi, one_mul,
        mul_one] at this
    · intro h; rw [h, mul_zero, zero_mul]
  have ψne : ∀ {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {n : ℤ}, nrd z = (n : ℚ) → ¬ ((ℓ : ℤ) ^ 2 ∣ n) → ψ z ≠ 0 := by
    intro z hz n hzn hn h0
    obtain ⟨y, hy, e⟩ := (ψzero_iff hz).1 h0
    exact not_smul_of_nrd hΛo hℓ hzn hn y hy e
  have ψℓ : ψ (((ℓ : ℚ) : ℍ[ℚ, a, b])) = 0 := by rw [hψ, Φℓ, mul_zero, zero_mul]
  have ψone : ψ 1 = 1 := by rw [hψ, Φone, mul_one, hPiP]

  have hPiw₀ : Pinv *ᵥ w₀ = Pi.single 0 1 := by
    have : P *ᵥ (Pi.single (0 : Fin 2) (1 : ZMod ℓ)) = w₀ := by rw [mulVec_eq_col_zero]; funext i; exact hPcol i
    rw [← this, Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
  have colzero_iff : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod ℓ), (∀ i, (Pinv * B * P) i 0 = 0) ↔ B *ᵥ w₀ = 0 := by
    intro B
    have e : ∀ i, (Pinv * B * P) i 0 = (Pinv *ᵥ (B *ᵥ w₀)) i := fun i => conj_apply_zero Pinv B P w₀ hPcol i
    constructor
    · intro h
      have h' : Pinv *ᵥ (B *ᵥ w₀) = 0 := by funext i; rw [← e i]; exact h i
      have : P *ᵥ (Pinv *ᵥ (B *ᵥ w₀)) = 0 := by rw [h', Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hPPi, Matrix.one_mulVec] at this
    · intro h i; rw [e i, h, Matrix.mulVec_zero]; rfl
  have hcolJ : ∀ y ∈ J', ∀ i, ψ ((N : ℤ) • y) i 0 = 0 := by
    intro y hy
    rw [hψ, colzero_iff, ← hann, hImem]
    exact ⟨y, hy, rfl⟩

  let E : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![0, 1; 0, 0]
  have hE : ∀ i j, E i j = if i = 0 ∧ j = 1 then 1 else 0 := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨yE, hyE, hEeq⟩ : ∃ y ∈ J', ψ ((N : ℤ) • y) = E := by
    have hB : (P * E * Pinv) *ᵥ w₀ = 0 := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPiw₀]
      have : E *ᵥ (Pi.single (0 : Fin 2) (1 : ZMod ℓ)) = 0 := by rw [mulVec_eq_col_zero]; funext i; fin_cases i <;> rfl
      rw [this, Matrix.mulVec_zero]
    obtain ⟨y, hy, e⟩ := (hImem _).1 ((hann _).2 hB)
    refine ⟨y, hy, ?_⟩
    rw [hψ, ← e, show Pinv * (P * E * Pinv) * P = (Pinv * P) * E * (Pinv * P) by simp only [mul_assoc], hPiP, one_mul, mul_one]
  have hNJR : ∀ y ∈ J', ((N : ℤ) • y) ∈ R := by
    intro y hy
    refine (h5 _ (h3 y hy)).2 fun j hj => ?_
    rw [mul_smul_comm, ← smul_mul_assoc]
    exact h2 _ (h3 j hj) y hy
  have hrE : ((N : ℤ) • yE) ∈ R := hNJR yE hyE

  have hupper : ∀ r ∈ R, ψ r 1 0 = 0 := by
    intro r hr
    have hm : ((N : ℤ) • yE) * r = (N : ℤ) • (yE * r) := smul_mul_assoc _ _ _
    have hyr : yE * r ∈ J' := (h5 r (hRΛ hr)).1 hr yE hyE
    have := hcolJ (yE * r) hyr 0
    rw [← hm, ψmul (h3 yE hyE) (hRΛ hr), hEeq, mul_apply_two] at this
    simpa [hE] using this

  have hstΛ : star t ∈ Λ := star_mem' hΛo htΛ
  have hsxΛ : star x ∈ Λ := star_mem' hΛo hxΛ
  have hstR : star t ∈ R := star_mem' hRo ht
  have hsxR : star x ∈ R := star_mem' hRo hxR

  have hpair : ∀ z ∈ R, nrd z = (ℓ : ℚ) →
      ψ z * ψ (star z) = 0 ∧ ψ (star z) * ψ z = 0 ∧ ψ z ≠ 0 ∧ ψ (star z) ≠ 0 ∧
      ψ z 1 0 = 0 ∧ ψ (star z) 1 0 = 0 ∧ ψ (star z) 1 1 = ψ z 0 0 ∧ ψ (star z) 0 0 = ψ z 1 1 := by
    intro z hzR hzn
    have hzΛ := hRΛ hzR
    have hszR := star_mem' hRo hzR
    have hszΛ := hRΛ hszR
    have hZZb : ψ z * ψ (star z) = 0 := by rw [← ψmul hzΛ hszΛ, mul_star_eq_coe_nrd, hzn, ψℓ]
    have hZbZ : ψ (star z) * ψ z = 0 := by rw [← ψmul hszΛ hzΛ, star_mul_eq_coe_nrd, hzn, ψℓ]
    have hZ0 : ψ z ≠ 0 := ψne hzΛ (n := ℓ) (by rw [hzn]; norm_cast) hℓsq
    have hZb0 : ψ (star z) ≠ 0 := ψne hszΛ (n := ℓ) (by rw [nrd_star', hzn]; norm_cast) hℓsq
    have hZ10 := hupper z hzR
    have hZb10 := hupper _ hszR

    obtain ⟨τ, hτ⟩ := (hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hzΛ).2
    have hsum : ψ z + ψ (star z) = (τ : ZMod ℓ) • 1 := by
      rw [← ψadd hzΛ hszΛ, add_star_eq_coe_trd, ← hτ,
        show (((τ : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (τ : ℤ) • (1 : ℍ[ℚ, a, b]) by
          rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one], ψzsmul τ hΛo.one_mem, ψone]
      norm_cast

    have e00 : ψ z 0 0 + ψ (star z) 0 0 = τ := by
      have := congrFun (congrFun hsum 0) 0; simpa using this
    have e11 : ψ z 1 1 + ψ (star z) 1 1 = τ := by
      have := congrFun (congrFun hsum 1) 1; simpa using this
    have e01 : ψ z 0 1 + ψ (star z) 0 1 = 0 := by
      have := congrFun (congrFun hsum 0) 1; simpa using this

    have p11 : ψ z 1 1 * ψ (star z) 1 1 = 0 := by
      have := congrFun (congrFun hZZb 1) 1; rw [mul_apply_two, hZ10] at this; simpa using this
    have p00 : ψ z 0 0 * ψ (star z) 0 0 = 0 := by
      have := congrFun (congrFun hZZb 0) 0; rw [mul_apply_two, hZb10] at this; simpa using this
    have p01 : ψ z 0 0 * ψ (star z) 0 1 + ψ z 0 1 * ψ (star z) 1 1 = 0 := by
      have := congrFun (congrFun hZZb 0) 1; rw [mul_apply_two] at this; simpa using this

    have key1 : ψ (star z) 1 1 = ψ z 0 0 := by
      by_cases h00 : ψ z 0 0 = 0
      ·

        by_contra hne'
        have hzb11 : ψ (star z) 1 1 ≠ 0 := by intro h; exact hne' (by rw [h, h00])
        have q11 : ψ (star z) 1 1 * ψ z 1 1 = 0 := by
          have := congrFun (congrFun hZbZ 1) 1; rw [mul_apply_two, hZb10] at this; simpa using this
        have hz11 : ψ z 1 1 = 0 := by
          rcases mul_eq_zero.1 q11 with h | h
          · exact absurd h hzb11
          · exact h
        have hz01 : ψ z 0 1 ≠ 0 := by
          intro h; apply hZ0; ext i j; fin_cases i <;> fin_cases j
          · exact h00
          · exact h
          · exact hZ10
          · exact hz11
        have q01 : ψ (star z) 0 0 * ψ z 0 1 + ψ (star z) 0 1 * ψ z 1 1 = 0 := by
          have := congrFun (congrFun hZbZ 0) 1; rw [mul_apply_two] at this; simpa using this
        rw [hz11, mul_zero, add_zero] at q01
        have hzb00 : ψ (star z) 0 0 = 0 := by
          rcases mul_eq_zero.1 q01 with h | h
          · exact h
          · exact absurd h hz01

        have hτ0 : (τ : ZMod ℓ) = 0 := by rw [← e00, h00, hzb00, add_zero]
        apply hzb11
        have := e11; rw [hz11, zero_add, hτ0] at this; exact this
      ·

        have hzb00 : ψ (star z) 0 0 = 0 := by
          rcases mul_eq_zero.1 p00 with h | h
          · exact absurd h h00
          · exact h
        have hτ' : (τ : ZMod ℓ) = ψ z 0 0 := by rw [← e00, hzb00, add_zero]
        by_cases hzb11 : ψ (star z) 1 1 = 0
        · exfalso
          have hz11 : ψ z 1 1 = ψ z 0 0 := by rw [← hτ', ← e11, hzb11, add_zero]
          rw [hzb11, mul_zero, add_zero] at p01
          have hzb01 : ψ (star z) 0 1 = 0 := by
            rcases mul_eq_zero.1 p01 with h | h
            · exact absurd h h00
            · exact h
          apply hZb0; ext i j; fin_cases i <;> fin_cases j
          · exact hzb00
          · exact hzb01
          · exact hZb10
          · exact hzb11
        · have hz11 : ψ z 1 1 = 0 := by
            rcases mul_eq_zero.1 p11 with h | h
            · exact h
            · exact absurd h hzb11
          rw [← hτ', ← e11, hz11, zero_add]
    have key2 : ψ (star z) 0 0 = ψ z 1 1 := by

      have := e00; rw [← e11, key1] at this

      linear_combination this
    exact ⟨hZZb, hZbZ, hZ0, hZb0, hZ10, hZb10, key1, key2⟩
  obtain ⟨hTTb, hTbT, hT0, hTb0, hT10, hTb10, hTb11, hTb00⟩ := hpair t ht hnt
  obtain ⟨hXXb, hXbX, hX0, hXb0, hX10, hXb10, hXb11, hXb00⟩ := hpair x hxR hnx

  have hW10 : ψ (w : ℍ[ℚ, a, b]) 1 0 = 0 := hupper _ hwR
  have hW0 : ψ (w : ℍ[ℚ, a, b]) ≠ 0 := ψne hwΛ (n := N) (by rw [hwn]; norm_cast) hℓsqN
  have hswR : star (w : ℍ[ℚ, a, b]) ∈ R := star_mem' hRo hwR
  have hnatΛ : ∀ n : ℕ, ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    intro n
    rw [show ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℚ) • 1 by rw [← coe_mul_eq_smul, mul_one], ← natCast_zsmul_eq_ratCast_smul]
    exact Λ.smul_mem _ hΛo.one_mem
  have hNcoe : (((N : ℕ) : ℚ) : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * ((M : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hM]; push_cast; rfl
  have hWWb : ψ (w : ℍ[ℚ, a, b]) * ψ (star (w : ℍ[ℚ, a, b])) = 0 := by
    rw [← ψmul hwΛ (hRΛ hswR), mul_star_eq_coe_nrd, hwn, hNcoe, ψmul (hnatΛ ℓ) (hnatΛ M), ψℓ, zero_mul]
  have hWb0 : ψ (star (w : ℍ[ℚ, a, b])) ≠ 0 := ψne (hRΛ hswR) (n := N) (by rw [nrd_star', hwn]; norm_cast) hℓsqN
  have hWb10 : ψ (star (w : ℍ[ℚ, a, b])) 1 0 = 0 := hupper _ hswR
  have hdetW : ψ (w : ℍ[ℚ, a, b]) 0 0 * ψ (w : ℍ[ℚ, a, b]) 1 1 = 0 := by

    by_contra hne'
    obtain ⟨h00, h11⟩ := mul_ne_zero_iff.1 hne'
    apply hWb0
    have q11 : ψ (w : ℍ[ℚ, a, b]) 1 1 * ψ (star (w : ℍ[ℚ, a, b])) 1 1 = 0 := by
      have := congrFun (congrFun hWWb 1) 1; rw [mul_apply_two, hW10] at this; simpa using this
    have hb11 : ψ (star (w : ℍ[ℚ, a, b])) 1 1 = 0 := (mul_eq_zero.1 q11).elim (fun h => absurd h h11) id
    have q00 : ψ (w : ℍ[ℚ, a, b]) 0 0 * ψ (star (w : ℍ[ℚ, a, b])) 0 0 = 0 := by
      have := congrFun (congrFun hWWb 0) 0; rw [mul_apply_two, hWb10] at this; simpa using this
    have hb00 : ψ (star (w : ℍ[ℚ, a, b])) 0 0 = 0 := (mul_eq_zero.1 q00).elim (fun h => absurd h h00) id
    have q01 : ψ (w : ℍ[ℚ, a, b]) 0 0 * ψ (star (w : ℍ[ℚ, a, b])) 0 1 +
        ψ (w : ℍ[ℚ, a, b]) 0 1 * ψ (star (w : ℍ[ℚ, a, b])) 1 1 = 0 := by
      have := congrFun (congrFun hWWb 0) 1; rw [mul_apply_two] at this; simpa using this
    rw [hb11, mul_zero, add_zero] at q01
    have hb01 : ψ (star (w : ℍ[ℚ, a, b])) 0 1 = 0 := (mul_eq_zero.1 q01).elim (fun h => absurd h h00) id
    ext i j; fin_cases i <;> fin_cases j
    · exact hb00
    · exact hb01
    · exact hWb10
    · exact hb11

  obtain ⟨hW00, hW11⟩ : ψ (w : ℍ[ℚ, a, b]) 0 0 = 0 ∧ ψ (w : ℍ[ℚ, a, b]) 1 1 = 0 := by

    set rEl : ℍ[ℚ, a, b] := (N : ℤ) • yE with hrEl
    have hr' : (w : ℍ[ℚ, a, b]) * rEl * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := (hwnorm rEl).1 hrE
    have hr'' : ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * rEl * (w : ℍ[ℚ, a, b]) ∈ R := by
      apply (hwnorm _).2
      rw [show (w : ℍ[ℚ, a, b]) * (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * rEl * (w : ℍ[ℚ, a, b])) *
          ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = rEl by
        simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]]
      exact hrE
    have eA : ψ ((w : ℍ[ℚ, a, b]) * rEl * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) * ψ (w : ℍ[ℚ, a, b]) =
        ψ (w : ℍ[ℚ, a, b]) * E := by
      rw [← hEeq, ← ψmul (hRΛ hr') hwΛ, ← ψmul hwΛ (hRΛ hrE), Units.inv_mul_cancel_right]
    have eB : E * ψ (w : ℍ[ℚ, a, b]) =
        ψ (w : ℍ[ℚ, a, b]) * ψ (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * rEl * (w : ℍ[ℚ, a, b])) := by
      rw [← hEeq, ← ψmul (hRΛ hrE) hwΛ, ← ψmul hwΛ (hRΛ hr''), ← mul_assoc, ← mul_assoc,
        Units.mul_inv, one_mul]
    set U' := ψ ((w : ℍ[ℚ, a, b]) * rEl * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) with hU'
    set U'' := ψ (((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * rEl * (w : ℍ[ℚ, a, b])) with hU''
    set W := ψ (w : ℍ[ℚ, a, b]) with hW
    have hU'10 : U' 1 0 = 0 := hupper _ hr'
    have hU''10 : U'' 1 0 = 0 := hupper _ hr''

    have a00 : U' 0 0 * W 0 0 = 0 := by
      have := congrFun (congrFun eA 0) 0; rw [mul_apply_two, mul_apply_two, hW10] at this; simpa [hE] using this
    have a01 : U' 0 0 * W 0 1 + U' 0 1 * W 1 1 = W 0 0 := by
      have := congrFun (congrFun eA 0) 1; rw [mul_apply_two, mul_apply_two] at this; simpa [hE] using this

    have b01 : W 1 1 = W 0 0 * U'' 0 1 + W 0 1 * U'' 1 1 := by
      have := congrFun (congrFun eB 0) 1; rw [mul_apply_two, mul_apply_two] at this; simpa [hE] using this
    have b11 : W 1 1 * U'' 1 1 = 0 := by
      have := congrFun (congrFun eB 1) 1; rw [mul_apply_two, mul_apply_two, hW10] at this; simpa [hE, hU''10] using this
    have hW00 : W 0 0 = 0 := by
      by_contra h00
      have h11 : W 1 1 = 0 := (mul_eq_zero.1 hdetW).elim (fun h => absurd h h00) id
      have hu : U' 0 0 = 0 := (mul_eq_zero.1 a00).elim id (fun h => absurd h h00)
      rw [hu, zero_mul, zero_add, h11, mul_zero] at a01
      exact h00 a01.symm
    refine ⟨hW00, ?_⟩
    rw [hW00, zero_mul, zero_add] at b01
    rcases mul_eq_zero.1 b11 with h | h
    · exact h
    · rw [h, mul_zero] at b01; exact b01
  have hW01 : ψ (w : ℍ[ℚ, a, b]) 0 1 ≠ 0 := by
    intro h; apply hW0; ext i j; fin_cases i <;> fin_cases j
    · exact hW00
    · exact h
    · exact hW10
    · exact hW11

  have hXW : ψ x * ψ (w : ℍ[ℚ, a, b]) = ψ (w : ℍ[ℚ, a, b]) * ψ t := by
    rw [← ψmul hxΛ hwΛ, hxw, ψmul hwΛ htΛ]
  have hXbW : ψ (star x) * ψ (w : ℍ[ℚ, a, b]) = ψ (w : ℍ[ℚ, a, b]) * ψ (star t) := by
    rw [← ψmul hsxΛ hwΛ, hxbw, ψmul hwΛ hstΛ]
  have hX00 : ψ x 0 0 = ψ t 1 1 := by
    have := congrFun (congrFun hXW 0) 1
    rw [mul_apply_two, mul_apply_two, hW11, hW00] at this
    simp only [mul_zero, add_zero, zero_mul, zero_add] at this
    exact mul_right_cancel₀ hW01 (this.trans (mul_comm _ _))
  have hX11 : ψ x 1 1 = ψ t 0 0 := by
    have := congrFun (congrFun hXbW 0) 1
    rw [mul_apply_two, mul_apply_two, hW11, hW00] at this
    simp only [mul_zero, add_zero, zero_mul, zero_add] at this
    rw [← hXb00, ← hTb11]
    exact mul_right_cancel₀ hW01 (this.trans (mul_comm _ _))

  have hcop : IsCoprime (M : ℤ) (ℓ : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]; exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM))
  have hNsmul : ∀ y : ℍ[ℚ, a, b], (N : ℤ) • y = (ℓ : ℚ) • ((M : ℤ) • y) := by
    intro y; rw [hM, ← natCast_zsmul_eq_ratCast_smul, smul_smul]; norm_cast
  have hTiff : (∀ j ∈ J', j * star t ∈ Λ → j ∈ Λ) ↔ ψ t 0 0 ≠ 0 := by
    constructor
    · intro hTr h00

      have hETb : ψ ((N : ℤ) • yE) * ψ (star t) = 0 := by
        rw [hEeq]; ext i j; rw [mul_apply_two]
        fin_cases i <;> fin_cases j <;> simp [hE, hTb10, hTb11, h00]
      rw [← ψmul (h3 yE hyE) hstΛ] at hETb
      obtain ⟨z, hz, ez⟩ := (ψzero_iff (hΛo.mul_mem (h3 yE hyE) hstΛ)).1 hETb
      have hj : ((M : ℤ) • yE) * star t ∈ Λ := by
        have : (ℓ : ℚ) • (((M : ℤ) • yE) * star t) = (ℓ : ℚ) • z := by rw [← ez, ← smul_mul_assoc, ← hNsmul]
        rw [smul_right_injective _ hℓ0 this]; exact hz
      have hjΛ := hTr _ (J'.smul_mem _ hyE) hj
      have : ψ ((N : ℤ) • yE) = 0 := (ψzero_iff (h3 yE hyE)).2 ⟨(M : ℤ) • yE, hjΛ, hNsmul yE⟩
      rw [hEeq] at this
      have := congrFun (congrFun this 0) 1
      simp [hE] at this
    · intro h00 j hj hjt
      have hℓj : ((ℓ : ℕ) : ℤ) • j ∈ Λ := by
        rw [natCast_zsmul_eq_ratCast_smul, ← coe_mul_eq_smul, coe_commutes, ← hnt, ← star_mul_eq_coe_nrd, ← mul_assoc]
        exact hΛo.mul_mem hjt htΛ
      have hNj : ((N : ℕ) : ℤ) • j ∈ Λ := h3 j hj

      have hprod : ψ ((N : ℤ) • j) * ψ (star t) = 0 := by
        rw [← ψmul hNj hstΛ, smul_mul_assoc, ψzero_iff (Λ.smul_mem _ hjt)]
        exact ⟨(M : ℤ) • (j * star t), Λ.smul_mem _ hjt, hNsmul _⟩
      have hcol := hcolJ j hj
      have hz1 : ∀ i, ψ ((N : ℤ) • j) i 1 = 0 := by
        intro i
        have := congrFun (congrFun hprod i) 1
        rw [mul_apply_two, hcol i, zero_mul, zero_add, hTb11] at this
        exact (mul_eq_zero.1 this).elim id (fun h => absurd h h00)
      have hψ0 : ψ ((N : ℤ) • j) = 0 := by
        ext i k; fin_cases k
        · exact hcol i
        · exact hz1 i
      obtain ⟨z, hz, ez⟩ := (ψzero_iff hNj).1 hψ0
      have hMj : ((M : ℕ) : ℤ) • j ∈ Λ := by
        have : (ℓ : ℚ) • (((M : ℤ) • j)) = (ℓ : ℚ) • z := by rw [← ez, hNsmul]
        rw [smul_right_injective _ hℓ0 this]; exact hz
      obtain ⟨c, d, hcd⟩ := hcop
      have : j = c • (((M : ℕ) : ℤ) • j) + d • (((ℓ : ℕ) : ℤ) • j) := by
        rw [smul_smul, smul_smul, ← add_smul, hcd, one_smul]
      rw [this]; exact add_mem (Λ.smul_mem _ hMj) (Λ.smul_mem _ hℓj)

  have hconjΛ : ∀ r ∈ R, (((xu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * x ∈ Λ ↔ ψ (star x * r * x) = 0) := by
    intro r hr
    have hm : star x * r * x ∈ Λ := hΛo.mul_mem (hΛo.mul_mem hsxΛ (hRΛ hr)) hxΛ
    have hrel : star x * r * x = (ℓ : ℚ) • (((xu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * x) := by
      rw [hstarx, smul_mul_assoc, smul_mul_assoc]
    rw [ψzero_iff hm]
    constructor
    · intro h; exact ⟨_, h, hrel⟩
    · rintro ⟨z, hz, ez⟩
      rw [hrel] at ez
      rw [smul_right_injective _ hℓ0 ez]; exact hz
  have hSiff : (¬ ∀ r ∈ R, ((xu⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * x ∈ Λ) ↔ ψ x 1 1 ≠ 0 := by
    constructor
    · intro hS h11
      apply hS
      intro r hr
      rw [hconjΛ r hr, ψmul (hΛo.mul_mem hsxΛ (hRΛ hr)) hxΛ, ψmul hsxΛ (hRΛ hr)]
      have hr10 := hupper r hr
      ext i j; rw [mul_apply_two, mul_apply_two, mul_apply_two]
      fin_cases i <;> fin_cases j <;> simp [hX10, hXb10, hXb00, hXb11, h11, hr10] <;> ring_nf <;>
        simp [h11, hXb00, hX10]
    · intro h11 hall
      have := (hconjΛ _ hrE).1 (hall _ hrE)
      rw [ψmul (hΛo.mul_mem hsxΛ (hRΛ hrE)) hxΛ, ψmul hsxΛ (hRΛ hrE), hEeq] at this
      have := congrFun (congrFun this 0) 1
      rw [mul_apply_two, mul_apply_two, mul_apply_two] at this
      simp [hE, hX10, hXb00] at this
      exact h11 this
  rw [hTiff, hSiff, hX11]

end S_QuaternionAlgebra_IsEichlerOrder_forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_forall_mul_star_mem_imp_mem_iff_not_conj_eq_and_not_conj_le_of_dvd (solution)
