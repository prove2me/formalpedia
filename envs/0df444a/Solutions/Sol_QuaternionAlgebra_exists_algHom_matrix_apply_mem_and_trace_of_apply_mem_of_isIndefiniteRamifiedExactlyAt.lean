-- Prove2me | solution 1 for QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c8215806-6233-52df-8fca-8d091a296787

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.style.longFile 0
set_option maxHeartbeats 3200000

open scoped Quaternion TensorProduct
p2m_open "QuaternionAlgebra~nrd_mul IsDedekindDomain NumberField"

local infixr:73 " ⋇ " => HSMul.hSMul
local macro_rules | `($x ⋇ $y) => `(leftact% HSMul.hSMul $x $y)

namespace P2mTypeFix

section Generic

variable {A : Type*} [Ring A]

def conjAlgHom {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1) (h' : γ' * γ = 1) :
    A →ₐ[R] A where
  toFun x := γ' * x * γ
  map_one' := by rw [mul_one, h']
  map_mul' x y := by
    calc γ' * (x * y) * γ = γ' * x * (γ * γ') * y * γ := by rw [h]; noncomm_ring
      _ = γ' * x * γ * (γ' * y * γ) := by noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' x y := by rw [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, h']

theorem conjAlgHom_apply {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1)
    (h' : γ' * γ = 1) (x : A) : conjAlgHom (R := R) γ γ' h h' x = γ' * x * γ := rfl

theorem mul_mul_apply_eq_mulVec (γ' X γ : Matrix (Fin 2) (Fin 2) A) (i l : Fin 2) :
    (γ' * X * γ) i l = (γ'.mulVec (X.mulVec (γ.mulVec (Pi.single l 1)))) i := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end Generic

section Quat

variable {R : Type*} [CommRing R] {a b : R}

theorem nrd_mul (x y : ℍ[R, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk, nrd_mk]
  ring

theorem nrd_smul (r : R) (x : ℍ[R, a, b]) : nrd (r ⋇ x) = r ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [nrd]
  ring

theorem star_eq_trd_sub (x : ℍ[R, a, b]) : star x = ((trd x : R) : ℍ[R, a, b]) - x := by
  rw [← add_star_eq_coe_trd]; abel

theorem mul_self_eq (x : ℍ[R, a, b]) :
    x * x = ((trd x : R) : ℍ[R, a, b]) * x - ((nrd x : R) : ℍ[R, a, b]) := by
  have h1 := star_mul_eq_coe_nrd x
  rw [star_eq_trd_sub, sub_mul] at h1
  rw [← h1]; abel

theorem twist_identity (o p : ℍ[R, a, b]) :
    o * p - p * star o = ((trd p : R) : ℍ[R, a, b]) * o - ((trd (o * star p) : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := o
  obtain ⟨y₀, y₁, y₂, y₃⟩ := p
  ext <;> simp [trd] <;> ring

theorem nrd_eq_zero_iff {c d : ℚ} (hc : c < 0) (hd : d < 0) (x : ℍ[ℚ, c, d]) : nrd x = 0 ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    simp only [nrd_mk] at h
    have h0 : 0 ≤ x₀ ^ 2 := sq_nonneg _
    have h1 : 0 ≤ -c * x₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ -d * x₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h3 : 0 ≤ c * d * x₃ ^ 2 := mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg hc hd)) (sq_nonneg _)
    have e0 : x₀ ^ 2 = 0 := by nlinarith
    have e1 : -c * x₁ ^ 2 = 0 := by nlinarith
    have e2 : -d * x₂ ^ 2 = 0 := by nlinarith
    have e3 : c * d * x₃ ^ 2 = 0 := by nlinarith
    have hcd : c * d ≠ 0 := (mul_pos_of_neg_of_neg hc hd).ne'
    ext <;> simp_all [pow_eq_zero_iff, hc.ne, hd.ne]
  · rintro rfl; exact nrd_zero

end Quat

theorem cayley_two {F : Type*} [CommRing F] (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace ⋇ M - M.det ⋇ (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_intCast_of_pow_eq {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] {x : F}
    (hx : x ^ q = x) : ∃ k : ℤ, (k : F) = x :=
  (mem_bot_iff_intCast q F).1 ((Subfield.mem_bot_iff_pow_eq_self F q).2 hx)

structure IsChar {A : Type*} [Ring A] (O : Submodule ℤ A) {F : Type*} [Ring F] (χ : ↥O → F) : Prop where
  one : ∀ h : (1 : A) ∈ O, χ ⟨1, h⟩ = 1
  add : ∀ x y : ↥O, χ (x + y) = χ x + χ y
  mul : ∀ (x y : ↥O) (h : (x : A) * (y : A) ∈ O), χ ⟨(x : A) * (y : A), h⟩ = χ x * χ y

namespace IsChar

variable {A : Type*} [Ring A] {O : Submodule ℤ A} {F : Type*} [Ring F] {χ : ↥O → F}

def toAddMonoidHom (h : IsChar O χ) : ↥O →+ F := AddMonoidHom.mk' χ h.add

@[scoped simp] theorem toAddMonoidHom_apply (h : IsChar O χ) (x : ↥O) : h.toAddMonoidHom x = χ x := rfl

theorem map_zero (h : IsChar O χ) : χ 0 = 0 := by
  rw [← h.toAddMonoidHom_apply, _root_.map_zero]

theorem map_neg (h : IsChar O χ) (x : ↥O) : χ (-x) = -χ x := by
  rw [← h.toAddMonoidHom_apply, _root_.map_neg, h.toAddMonoidHom_apply]

theorem map_sub (h : IsChar O χ) (x y : ↥O) : χ (x - y) = χ x - χ y := by
  rw [← h.toAddMonoidHom_apply, _root_.map_sub, h.toAddMonoidHom_apply, h.toAddMonoidHom_apply]

theorem map_zsmul (h : IsChar O χ) (n : ℤ) (x : ↥O) : χ (n ⋇ x) = n ⋇ χ x := by
  rw [← h.toAddMonoidHom_apply, _root_.map_zsmul, h.toAddMonoidHom_apply]

theorem mul' (h : IsChar O χ) {x y : A} (hx : x ∈ O) (hy : y ∈ O) (hxy : x * y ∈ O) :
    χ ⟨x * y, hxy⟩ = χ ⟨x, hx⟩ * χ ⟨y, hy⟩ := h.mul ⟨x, hx⟩ ⟨y, hy⟩ hxy

theorem add' (h : IsChar O χ) {x y : A} (hx : x ∈ O) (hy : y ∈ O) :
    χ ⟨x + y, O.add_mem hx hy⟩ = χ ⟨x, hx⟩ + χ ⟨y, hy⟩ := h.add ⟨x, hx⟩ ⟨y, hy⟩

theorem sub' (h : IsChar O χ) {x y : A} (hx : x ∈ O) (hy : y ∈ O) :
    χ ⟨x - y, O.sub_mem hx hy⟩ = χ ⟨x, hx⟩ - χ ⟨y, hy⟩ := h.map_sub ⟨x, hx⟩ ⟨y, hy⟩

theorem congr (h : IsChar O χ) {x y : A} (hxy : x = y) (hx : x ∈ O) (hy : y ∈ O) :
    χ ⟨x, hx⟩ = χ ⟨y, hy⟩ := by subst hxy; rfl

end IsChar
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar"

section CharQuat

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]} {F : Type*} [Ring F] {χ : ↥O → F}

theorem intCast_mem (hO : IsOrder O) (k : ℤ) : ((k : ℚ) : ℍ[ℚ, a, b]) ∈ O := by
  have : ((k : ℚ) : ℍ[ℚ, a, b]) = k ⋇ (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact O.smul_mem k hO.one_mem

theorem IsChar.map_intCast (h : IsChar O χ) (hO : IsOrder O) (k : ℤ) (hk : ((k : ℚ) : ℍ[ℚ, a, b]) ∈ O) :
    χ ⟨(k : ℚ), hk⟩ = k := by
  have : (⟨(k : ℚ), hk⟩ : ↥O) = k ⋇ ⟨1, hO.one_mem⟩ := by
    apply Subtype.ext
    simp only [SetLike.val_smul, zsmul_eq_mul, mul_one]
    norm_cast
  rw [this, h.map_zsmul, h.one, zsmul_eq_mul, mul_one]

end CharQuat
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar"

section Dichotomy

variable {a b c d : ℚ} {F : Type*} [Field F]

def rho (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (χ : ↥O → F) (m : ↥Λ) : Matrix (Fin 2) (Fin 2) F :=
  fun i l => χ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩

variable (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
  {O : Submodule ℤ ℍ[ℚ, c, d]} (hΛ : IsOrder Λ) (hO : IsOrder O)
  (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O) {χ : ↥O → F} (hχ : IsChar O χ)

theorem rho_apply (m : ↥Λ) (i l : Fin 2) : rho j Λ O hj χ m i l = χ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩ := rfl

include hΛ hO hχ in
theorem rho_one : rho j Λ O hj χ ⟨1, hΛ.one_mem⟩ = 1 := by
  ext i l
  rw [rho_apply]
  have h1 : j ((⟨1, hΛ.one_mem⟩ : ↥Λ) : ℍ[ℚ, a, b]) i l = (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l := by
    simp
  fin_cases i <;> fin_cases l
  · simpa [hχ.congr h1] using hχ.one hO.one_mem
  · have h__af := hχ.map_zero
    simp [hχ.congr h1] at h__af ⊢
    exact h__af
  · have h__af := hχ.map_zero
    simp [hχ.congr h1] at h__af ⊢
    exact h__af
  · simpa [hχ.congr h1] using hχ.one hO.one_mem

include hχ in
theorem rho_add (m m' : ↥Λ) : rho j Λ O hj χ (m + m') = rho j Λ O hj χ m + rho j Λ O hj χ m' := by
  ext i l
  simp only [rho_apply, Matrix.add_apply]
  rw [← hχ.add']
  exact hχ.congr (by simp) _ _

include hO hχ in
theorem rho_mul (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ) :
    rho j Λ O hj χ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = rho j Λ O hj χ m * rho j Λ O hj χ m' := by
  ext i l
  simp only [rho_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hmem0 : j (m : ℍ[ℚ, a, b]) i 0 * j (m' : ℍ[ℚ, a, b]) 0 l ∈ O := hO.mul_mem (hj m i 0) (hj m' 0 l)
  have hmem1 : j (m : ℍ[ℚ, a, b]) i 1 * j (m' : ℍ[ℚ, a, b]) 1 l ∈ O := hO.mul_mem (hj m i 1) (hj m' 1 l)
  rw [← hχ.mul' (hj m i 0) (hj m' 0 l) hmem0, ← hχ.mul' (hj m i 1) (hj m' 1 l) hmem1, ← hχ.add']
  refine hχ.congr ?_ _ _
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]

include hχ in

def rhoHom : ↥Λ →+ Matrix (Fin 2) (Fin 2) F := AddMonoidHom.mk' (rho j Λ O hj χ) (rho_add j hj hχ)

include hχ in
theorem rho_zsmul (n : ℤ) (m : ↥Λ) : rho j Λ O hj χ (n ⋇ m) = n ⋇ rho j Λ O hj χ m :=
  map_zsmul (rhoHom j hj hχ) n m

def IsScalarShape (M : Matrix (Fin 2) (Fin 2) F) : Prop := M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1

theorem isScalarShape_smul_one (s : F) : IsScalarShape (s ⋇ (1 : Matrix (Fin 2) (Fin 2) F)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem isScalarShape_add_iff {M N : Matrix (Fin 2) (Fin 2) F} (hN : IsScalarShape N) :
    IsScalarShape (M + N) ↔ IsScalarShape M := by
  obtain ⟨h1, h2, h3⟩ := hN
  simp only [IsScalarShape, Matrix.add_apply, h1, h2, h3, add_zero]
  constructor
  · rintro ⟨e1, e2, e3⟩; exact ⟨e1, e2, add_right_cancel e3⟩
  · rintro ⟨e1, e2, e3⟩; exact ⟨e1, e2, by rw [e3]⟩

theorem trace_eq_of_isScalarShape {M : Matrix (Fin 2) (Fin 2) F} (h : IsScalarShape M) :
    M = M 0 0 ⋇ (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨h1, h2, h3⟩ := h
  ext i l; fin_cases i <;> fin_cases l <;> simp [h1, h2, h3]

include hΛ hO hχ in

theorem trace_rho_eq_or_isScalarShape (m : ↥Λ) :
    (∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        (rho j Λ O hj χ m).trace = n) ∨
      IsScalarShape (rho j Λ O hj χ m) := by
  classical
  obtain ⟨⟨t, N, ht, hN⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hΛ m.2
  set M := rho j Λ O hj χ m with hM

  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.one_mem
  have hsq : (⟨(m : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), hΛ.mul_mem m.2 m.2⟩ : ↥Λ) =
      t ⋇ m - N ⋇ ⟨1, h1Λ⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, SetLike.val_smul, zsmul_eq_mul, mul_one]
    rw [mul_self_eq, ht, hN]
    norm_cast
  have hρsq : M * M = (t : F) ⋇ M - (N : F) ⋇ (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hM, ← rho_mul j hO hj hχ m m (hΛ.mul_mem m.2 m.2), hsq]
    change rhoHom j hj hχ (t ⋇ m - N ⋇ ⟨1, h1Λ⟩) = _
    rw [map_sub, map_zsmul, map_zsmul]
    change t ⋇ rho j Λ O hj χ m - N ⋇ rho j Λ O hj χ ⟨1, h1Λ⟩ = _
    rw [rho_one j hΛ hO hj hχ, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hCH := cayley_two M
  have hkey : (M.trace - (t : F)) ⋇ M = (M.det - (N : F)) ⋇ (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [sub_smul, sub_smul]
    have : M.trace ⋇ M - M.det ⋇ (1 : Matrix (Fin 2) (Fin 2) F) =
        (t : F) ⋇ M - (N : F) ⋇ (1 : Matrix (Fin 2) (Fin 2) F) := by rw [← hCH, hρsq]
    exact sub_eq_sub_iff_sub_eq_sub.1 this
  by_cases htr : M.trace = (t : F)
  · left
    intro n hn
    have : (t : ℚ) = n := by
      rw [add_star_eq_coe_trd, ht] at hn
      exact_mod_cast (QuaternionAlgebra.coe_injective hn)
    have htn : t = n := by exact_mod_cast this
    rw [htr, htn]
  · right
    have hne : M.trace - (t : F) ≠ 0 := sub_ne_zero.2 htr
    have : M = ((M.trace - (t : F))⁻¹ * (M.det - (N : F))) ⋇ (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [mul_smul, ← hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact isScalarShape_smul_one _

include hΛ hO hχ in

theorem dichotomy :
    (∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        (rho j Λ O hj χ m).trace = n) ∨
      ∀ m : ↥Λ, IsScalarShape (rho j Λ O hj χ m) := by
  by_cases hall : ∀ m : ↥Λ, IsScalarShape (rho j Λ O hj χ m)
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨m₀, hm₀⟩ := hall
  have hP₀ := (trace_rho_eq_or_isScalarShape j hΛ hO hj hχ m₀).resolve_right hm₀
  intro m n hn
  rcases trace_rho_eq_or_isScalarShape j hΛ hO hj hχ m with hP | hS
  · exact hP n hn
  ·
    have hns : ¬ IsScalarShape (rho j Λ O hj χ (m₀ + m)) := by
      rw [rho_add j hj hχ, isScalarShape_add_iff hS]; exact hm₀
    have hP := (trace_rho_eq_or_isScalarShape j hΛ hO hj hχ (m₀ + m)).resolve_right hns
    obtain ⟨⟨t₀, N₀, ht₀, -⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hΛ m₀.2
    have hn₀ : (m₀ : ℍ[ℚ, a, b]) + star (m₀ : ℍ[ℚ, a, b]) = ((t₀ : ℚ) : ℍ[ℚ, a, b]) := by
      rw [add_star_eq_coe_trd, ht₀]
    have hsum : ((m₀ + m : ↥Λ) : ℍ[ℚ, a, b]) + star ((m₀ + m : ↥Λ) : ℍ[ℚ, a, b]) =
        (((t₀ + n : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
      rw [Int.cast_add, QuaternionAlgebra.coe_add, ← hn₀, ← hn, Submodule.coe_add, star_add]
      abel
    have h1 := hP (t₀ + n) hsum
    have h2 := hP₀ t₀ hn₀
    rw [rho_add j hj hχ, Matrix.trace_add, h2, Int.cast_add] at h1
    exact add_left_cancel h1

end Dichotomy
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar"

section PrimeO

variable {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
  (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
  {F : Type*} [Field F] [CharP F q] {χ : ↥O → F} (hχ : IsChar O χ)

theorem star_mem_of_isOrder {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨⟨t, N, ht, -⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  rw [star_eq_trd_sub, ht]
  exact Λ.sub_mem (intCast_mem hΛ t) hx

include hH in
theorem divisionAt : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
    ∀ x : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun v hv => (hH.2.2 v).2 hv

include hH hO hχ in

theorem residue_trace (x : ↥O) (n : ℤ) (hn : (x : ℍ[ℚ, c, d]) + star (x : ℍ[ℚ, c, d]) = ((n : ℚ) : ℍ[ℚ, c, d])) :
    χ x + χ x ^ q = n :=
  IsOrder.apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit q (divisionAt q hH) O hO.1 F χ
    hχ.one hχ.add hχ.mul x n hn

include hH hO hχ in

theorem apply_star {x : ℍ[ℚ, c, d]} (hx : x ∈ O) (hx' : star x ∈ O) :
    χ ⟨star x, hx'⟩ = χ ⟨x, hx⟩ ^ q := by
  obtain ⟨⟨t, N, ht, -⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hx
  have hn : x + star x = ((t : ℚ) : ℍ[ℚ, c, d]) := by rw [add_star_eq_coe_trd, ht]
  have h1 := residue_trace q hH O hO hχ ⟨x, hx⟩ t hn
  have h2 : χ ⟨star x, hx'⟩ = t - χ ⟨x, hx⟩ := by
    have hst : star x = ((t : ℚ) : ℍ[ℚ, c, d]) - x := by rw [star_eq_trd_sub, ht]
    have htO := intCast_mem hO.1 t
    rw [hχ.congr hst hx' (O.sub_mem htO hx), hχ.sub' htO hx, hχ.map_intCast hO.1 t htO]
  rw [h2, ← h1]; ring

include hH hO hχ in

theorem apply_mul_apply_pow (x : ℍ[ℚ, c, d]) (hx : x ∈ O) (N : ℤ) (hN : nrd x = N) :
    χ ⟨x, hx⟩ * χ ⟨x, hx⟩ ^ q = N := by
  have hx' : star x ∈ O := star_mem_of_isOrder hO.1 hx
  rw [← apply_star q hH O hO hχ hx hx', ← hχ.mul' hx hx' (hO.1.mul_mem hx hx')]
  rw [hχ.congr (mul_star_eq_coe_nrd x) _ (by rw [hN]; exact intCast_mem hO.1 N)]
  rw [hχ.congr (by rw [hN]) _ (intCast_mem hO.1 N), hχ.map_intCast hO.1]

include hH hO hχ in

theorem apply_eq_zero_iff (x : ℍ[ℚ, c, d]) (hx : x ∈ O) :
    χ ⟨x, hx⟩ = 0 ↔ ∃ n : ℤ, nrd x = (q : ℚ) * n := by
  obtain ⟨⟨t, N, -, hN⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hx
  have key := apply_mul_apply_pow q hH O hO hχ x hx N hN
  constructor
  · intro h0
    rw [h0, zero_mul] at key
    have hdvd : (q : ℤ) ∣ N := (CharP.intCast_eq_zero_iff F q N).1 key.symm
    obtain ⟨n, rfl⟩ := hdvd
    exact ⟨n, by rw [hN]; push_cast; ring⟩
  · rintro ⟨n, hn⟩
    have hNq : N = q * n := by
      have : (N : ℚ) = (q : ℚ) * n := by rw [← hN, hn]
      exact_mod_cast this
    have h0 : (N : F) = 0 := by rw [hNq]; push_cast; rw [CharP.cast_eq_zero F q, zero_mul]
    rw [h0, ← pow_succ'] at key
    exact pow_eq_zero_iff (n := q + 1) (by omega) |>.1 key

def kerSub (O : Submodule ℤ ℍ[ℚ, c, d]) (χ : ↥O → F) (hχ : IsChar O χ) : Submodule ℤ ℍ[ℚ, c, d] where
  carrier := {x | ∃ hx : x ∈ O, χ ⟨x, hx⟩ = 0}
  add_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    exact ⟨O.add_mem hx hy, by rw [hχ.add' hx hy, hx0, hy0, add_zero]⟩
  zero_mem' := ⟨O.zero_mem, hχ.map_zero⟩
  smul_mem' := by
    rintro n x ⟨hx, hx0⟩
    refine ⟨O.smul_mem n hx, ?_⟩
    have := hχ.map_zsmul n ⟨x, hx⟩
    rw [hx0, smul_zero] at this
    exact this

theorem mem_kerSub_iff {x : ℍ[ℚ, c, d]} : x ∈ kerSub O χ hχ ↔ ∃ hx : x ∈ O, χ ⟨x, hx⟩ = 0 := Iff.rfl

theorem kerSub_le : kerSub O χ hχ ≤ O := fun _ ⟨hx, _⟩ => hx

include hH hO in
theorem mem_kerSub_iff_nrd {x : ℍ[ℚ, c, d]} :
    x ∈ kerSub O χ hχ ↔ x ∈ O ∧ ∃ n : ℤ, nrd x = (q : ℚ) * n := by
  constructor
  · rintro ⟨hx, hx0⟩; exact ⟨hx, (apply_eq_zero_iff q hH O hO hχ x hx).1 hx0⟩
  · rintro ⟨hx, hn⟩; exact ⟨hx, (apply_eq_zero_iff q hH O hO hχ x hx).2 hn⟩

include hH hO in

theorem apply_eq_zero_iff_mem_kerSub {F' : Type*} [Field F'] [CharP F' q] {χ' : ↥O → F'} (hχ' : IsChar O χ')
    {x : ℍ[ℚ, c, d]} (hx : x ∈ O) : χ' ⟨x, hx⟩ = 0 ↔ x ∈ kerSub O χ hχ := by
  rw [apply_eq_zero_iff q hH O hO hχ' x hx, mem_kerSub_iff_nrd q hH O hO hχ]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

theorem mul_mem_kerSub_left (hO1 : IsOrder O) {o p : ℍ[ℚ, c, d]} (ho : o ∈ O) (hp : p ∈ kerSub O χ hχ) :
    o * p ∈ kerSub O χ hχ := by
  obtain ⟨hp, hp0⟩ := hp
  exact ⟨hO1.mul_mem ho hp, by rw [hχ.mul' ho hp, hp0, mul_zero]⟩

theorem mul_mem_kerSub_right (hO1 : IsOrder O) {o p : ℍ[ℚ, c, d]} (hp : p ∈ kerSub O χ hχ) (ho : o ∈ O) :
    p * o ∈ kerSub O χ hχ := by
  obtain ⟨hp, hp0⟩ := hp
  exact ⟨hO1.mul_mem hp ho, by rw [hχ.mul' hp ho, hp0, zero_mul]⟩

theorem zsmul_mem_kerSub (hO1 : IsOrder O) {o : ℍ[ℚ, c, d]} (ho : o ∈ O) : (q : ℤ) ⋇ o ∈ kerSub O χ hχ := by
  refine ⟨O.smul_mem _ ho, ?_⟩
  have := hχ.map_zsmul (q : ℤ) ⟨o, ho⟩
  rw [zsmul_eq_mul, Int.cast_natCast, CharP.cast_eq_zero F q, zero_mul] at this
  exact this

theorem intCast_mem_kerSub (hO1 : IsOrder O) (k : ℤ) : (((q * k : ℤ) : ℚ) : ℍ[ℚ, c, d]) ∈ kerSub O χ hχ := by
  have : (((q * k : ℤ) : ℚ) : ℍ[ℚ, c, d]) = (q : ℤ) ⋇ (((k : ℤ) : ℚ) : ℍ[ℚ, c, d]) := by
    rw [zsmul_eq_mul, Int.cast_mul, QuaternionAlgebra.coe_mul]
    norm_cast
  rw [this]; exact zsmul_mem_kerSub q O hχ hO1 (intCast_mem hO1 k)

theorem sub_mem_kerSub_of_apply_eq {x y : ℍ[ℚ, c, d]} (hx : x ∈ O) (hy : y ∈ O) (h : χ ⟨x, hx⟩ = χ ⟨y, hy⟩) :
    x - y ∈ kerSub O χ hχ :=
  ⟨O.sub_mem hx hy, by rw [hχ.sub' hx hy, h, sub_self]⟩

include hH hO in
theorem star_mem_kerSub {p : ℍ[ℚ, c, d]} (hp : p ∈ kerSub O χ hχ) : star p ∈ kerSub O χ hχ := by
  obtain ⟨hp, hp0⟩ := hp
  have hp' := star_mem_of_isOrder hO.1 hp
  refine ⟨hp', ?_⟩
  rw [apply_star q hH O hO hχ hp hp', hp0, zero_pow (Fact.out : q.Prime).ne_zero]

include hH hO in

theorem exists_trd_eq_of_mem_kerSub {p : ℍ[ℚ, c, d]} (hp : p ∈ kerSub O χ hχ) :
    ∃ t : ℤ, trd p = ((q * t : ℤ) : ℚ) := by
  obtain ⟨hp, hp0⟩ := hp
  obtain ⟨⟨t, N, ht, -⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hp
  have hn : p + star p = ((t : ℚ) : ℍ[ℚ, c, d]) := by rw [add_star_eq_coe_trd, ht]
  have h1 := residue_trace q hH O hO hχ ⟨p, hp⟩ t hn
  rw [hp0, zero_pow (Fact.out : q.Prime).ne_zero, add_zero] at h1
  obtain ⟨k, rfl⟩ := (CharP.intCast_eq_zero_iff F q t).1 h1.symm
  exact ⟨k, ht⟩

include hH hO in

theorem exists_mul_eq_zsmul {p p' : ℍ[ℚ, c, d]} (hp : p ∈ kerSub O χ hχ) (hp' : p' ∈ kerSub O χ hχ) :
    ∃ z ∈ O, p * p' = (q : ℤ) ⋇ z := by
  rw [mem_kerSub_iff_nrd q hH O hO hχ] at hp hp'
  obtain ⟨hp, n, hn⟩ := hp
  obtain ⟨hp', n', hn'⟩ := hp'
  refine IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd (Fact.out : q.Prime) hH hO
    (hO.1.mul_mem hp hp') ?_
  by_cases hnn : (n : ℚ) * n' = 0
  · left
    rw [← nrd_eq_zero_iff hH.1 hH.2.1, nrd_mul, hn, hn']
    calc (q : ℚ) * n * ((q : ℚ) * n') = (q : ℚ) ^ 2 * (n * n') := by ring
      _ = 0 := by rw [hnn, mul_zero]
  · right
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    rw [nrd_mul, hn, hn', show (q : ℚ) * n * ((q : ℚ) * n') = (q : ℚ) ^ 2 * (n * n') by ring,
      padicValRat.mul (pow_ne_zero 2 hq0) hnn, padicValRat.pow _, padicValRat.self (Fact.out : q.Prime).one_lt]
    have : 0 ≤ padicValRat q ((n : ℚ) * n') := by
      rw [show ((n : ℚ) * n') = ((n * n' : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int]
      positivity
    push_cast
    linarith

include hH hO in

theorem exists_twist {o p : ℍ[ℚ, c, d]} (ho : o ∈ O) (hp : p ∈ kerSub O χ hχ) :
    ∃ z ∈ O, o * p - p * star o = (q : ℤ) ⋇ z := by
  obtain ⟨t, ht⟩ := exists_trd_eq_of_mem_kerSub q hH O hO hχ hp
  have hosp : o * star p ∈ kerSub O χ hχ :=
    mul_mem_kerSub_left O hχ hO.1 ho (star_mem_kerSub q hH O hO hχ hp)
  obtain ⟨t', ht'⟩ := exists_trd_eq_of_mem_kerSub q hH O hO hχ hosp
  refine ⟨((t : ℚ) : ℍ[ℚ, c, d]) * o - ((t' : ℚ) : ℍ[ℚ, c, d]),
    O.sub_mem (hO.1.mul_mem (intCast_mem hO.1 t) ho) (intCast_mem hO.1 t'), ?_⟩
  rw [twist_identity, ht, ht', zsmul_eq_mul, mul_sub, ← mul_assoc, Int.cast_mul, Int.cast_mul,
    QuaternionAlgebra.coe_mul, QuaternionAlgebra.coe_mul]
  norm_cast

include hH hO in

theorem exists_mem_kerSub_padicValRat_eq_one :
    ∃ h ∈ kerSub O χ hχ, padicValRat q (nrd h) = 1 := by
  obtain ⟨h, hh, hh0, hv⟩ := IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt q hH O hO
  refine ⟨h, ?_, hv⟩
  rw [mem_kerSub_iff_nrd q hH O hO hχ]
  refine ⟨hh, ?_⟩
  obtain ⟨⟨t, N, -, hN⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hh
  rw [hN, padicValRat.of_int] at hv
  have hv' : 1 ≤ padicValInt q N := by exact_mod_cast hv.ge
  have hdvd : (q : ℤ) ^ 1 ∣ N := (padicValInt_dvd_iff 1 N).2 (Or.inr hv')
  rw [pow_one] at hdvd
  obtain ⟨n, rfl⟩ := hdvd
  exact ⟨n, by rw [hN]; push_cast; ring⟩

include hH hO in

theorem not_dvd_unif_mul {h u z : ℍ[ℚ, c, d]} (hh : h ∈ O) (hv : padicValRat q (nrd h) = 1)
    (hu : u ∈ O) (huK : u ∉ kerSub O χ hχ) (hz : z ∈ O) (heq : h * u = (q : ℤ) ⋇ z) : False := by
  obtain ⟨⟨-, Nh, -, hNh⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hh
  obtain ⟨⟨-, Nu, -, hNu⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hu
  obtain ⟨⟨-, Nz, -, hNz⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hO.1 hz
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

  have hNu_ndvd : ¬ (q : ℤ) ∣ Nu := by
    rintro ⟨n, hn⟩
    exact huK ((mem_kerSub_iff_nrd q hH O hO hχ).2 ⟨hu, n, by rw [hNu, hn]; push_cast; ring⟩)
  have hNu0 : (Nu : ℚ) ≠ 0 := by
    have : Nu ≠ 0 := by rintro rfl; exact hNu_ndvd (dvd_zero _)
    exact_mod_cast this
  have hNh0 : (Nh : ℚ) ≠ 0 := by
    intro h0; rw [hNh, h0, padicValRat.zero] at hv; exact zero_ne_one hv
  have hval_lhs : padicValRat q (nrd (h * u)) = 1 := by
    rw [nrd_mul, hNh, hNu, padicValRat.mul hNh0 hNu0, ← hNh, hv, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hNu_ndvd]
    simp
  have hrhs : nrd ((q : ℤ) ⋇ z) = (q : ℚ) ^ 2 * Nz := by
    rw [← Int.cast_smul_eq_zsmul ℚ, nrd_smul, hNz]; push_cast; ring
  have hNz0 : (Nz : ℚ) ≠ 0 := by
    intro h0
    have : nrd (h * u) = 0 := by rw [heq, hrhs, h0, mul_zero]
    rw [this, padicValRat.zero] at hval_lhs
    exact zero_ne_one hval_lhs
  have hval_rhs : (2 : ℤ) ≤ padicValRat q (nrd ((q : ℤ) ⋇ z)) := by
    rw [hrhs, padicValRat.mul (pow_ne_zero 2 hq0) hNz0, padicValRat.pow _,
      padicValRat.self (Fact.out : q.Prime).one_lt, padicValRat.of_int]
    push_cast
    have : (0 : ℤ) ≤ padicValInt q Nz := by positivity
    linarith
  rw [heq] at hval_lhs
  rw [hval_lhs] at hval_rhs
  omega

end PrimeO
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar"

section ResidueLambda

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

theorem relIndex_le_sq (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (x₀ : ℍ[ℚ, a, b]) (hx₀ : x₀ ∈ Λ)
    (hgen : ∀ m ∈ Λ, ∃ (k k' : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧
      m = ((k : ℚ) : ℍ[ℚ, a, b]) + k' ⋇ x₀ + (q : ℤ) ⋇ y) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (q : ℤ) ⋇ y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.relIndex
        Λ.toAddSubgroup ≤ q ^ 2 := by
  classical
  set Q := Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (q : ℤ) ⋇ y) '' (Λ : Set ℍ[ℚ, a, b])) with hQ
  have hQmem : ∀ y ∈ Λ, (q : ℤ) ⋇ y ∈ Q := fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index]
  set A := Q.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup with hA
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos

  let rep : Fin q × Fin q → ↥Λ.toAddSubgroup := fun ij =>
    ⟨(((ij.1 : ℕ) : ℤ) : ℚ) + ((ij.2 : ℕ) : ℤ) ⋇ x₀, Λ.add_mem (intCast_mem hΛ _) (Λ.smul_mem _ hx₀)⟩
  let g : Fin q × Fin q → ↥Λ.toAddSubgroup ⧸ A := fun ij => QuotientAddGroup.mk (rep ij)
  have hg : Function.Surjective g := by
    rintro ⟨x, hx⟩
    change x ∈ Λ at hx
    obtain ⟨k, k', y, hy, hm⟩ := hgen x hx

    have hi := Int.emod_nonneg k hq0.ne'
    have hi' := Int.emod_nonneg k' hq0.ne'
    have hilt := Int.emod_lt_of_pos k hq0
    have hilt' := Int.emod_lt_of_pos k' hq0
    refine ⟨(⟨(k % q).toNat, by omega⟩, ⟨(k' % q).toNat, by omega⟩), ?_⟩
    change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, hA, AddSubgroup.mem_addSubgroupOf]
    change -((rep _ : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) + x ∈ Q
    simp only [rep]
    have e1 : (((k % q).toNat : ℕ) : ℤ) = k % q := Int.toNat_of_nonneg hi
    have e2 : (((k' % q).toNat : ℕ) : ℤ) = k' % q := Int.toNat_of_nonneg hi'
    rw [e1, e2, hm]
    have hk := Int.emod_add_mul_ediv k q
    have hk' := Int.emod_add_mul_ediv k' q
    set r := k % q
    set s := k / q
    set r' := k' % q
    set s' := k' / q
    have : -((((r : ℤ)) : ℚ) + (r' : ℤ) ⋇ x₀ : ℍ[ℚ, a, b]) +
        ((((k : ℤ)) : ℚ) + k' ⋇ x₀ + (q : ℤ) ⋇ y : ℍ[ℚ, a, b]) =
        (q : ℤ) ⋇ (((((s : ℤ)) : ℚ) : ℍ[ℚ, a, b]) + (s' : ℤ) ⋇ x₀ + y) := by
      rw [← hk, ← hk']
      simp only [zsmul_eq_mul]
      push_cast
      noncomm_ring
    rw [this]
    exact hQmem _ (Λ.add_mem (Λ.add_mem (intCast_mem hΛ _) (Λ.smul_mem _ hx₀)) hy)
  calc Nat.card (↥Λ.toAddSubgroup ⧸ A) ≤ Nat.card (Fin q × Fin q) := Nat.card_le_card_of_surjective g hg
    _ = q ^ 2 := by simp [sq]

theorem exists_pow_ne (hB : IsIndefiniteRamifiedExactlyAt a b q q') (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hΛ : IsMaximalOrder Λ) {F : Type*} [Field F] [CharP F q] (cΛ : ↥Λ → F) (hc : IsChar Λ cΛ) :
    ∃ m : ↥Λ, cΛ m ^ q ≠ cΛ m := by
  classical
  by_contra! H
  have hΛo : IsOrder Λ := hΛ.1
  have hq0F : ((q : ℤ) : F) = 0 := by rw [Int.cast_natCast]; exact CharP.cast_eq_zero F q
  have hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun v hv => (hB.2 v).2 (Or.inl hv)

  have hRT : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      cΛ m + cΛ m ^ q = n := fun m n hn =>
    IsOrder.apply_add_pow_eq_intCast_of_add_star_eq_of_forall_isUnit q hBq Λ hΛo F cΛ hc.one hc.add hc.mul m n hn

  have hint : ∀ m : ↥Λ, ∃ k : ℤ, (k : F) = cΛ m := fun m => exists_intCast_of_pow_eq q (H m)

  have hkill : ∀ (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ), (∃ n : ℤ, nrd x = (q : ℚ) * n) → cΛ ⟨x, hx⟩ = 0 := by
    intro x hx ⟨n, hn⟩
    obtain ⟨⟨t, N, ht, hN⟩, -⟩ := IsOrder.exists_int_trd_eq_and_nrd_eq hΛo hx
    have hx' : star x ∈ Λ := star_mem_of_isOrder hΛo hx
    have hn' : x + star x = ((t : ℚ) : ℍ[ℚ, a, b]) := by rw [add_star_eq_coe_trd, ht]
    have h1 := hRT ⟨x, hx⟩ t hn'
    rw [H] at h1

    have hst : star x = ((t : ℚ) : ℍ[ℚ, a, b]) - x := by rw [star_eq_trd_sub, ht]
    have htΛ := intCast_mem hΛo t
    have h2 : cΛ ⟨star x, hx'⟩ = cΛ ⟨x, hx⟩ := by
      rw [hc.congr hst hx' (Λ.sub_mem htΛ hx), hc.sub' htΛ hx, hc.map_intCast hΛo t htΛ, ← h1]; ring

    have hNq : (N : F) = 0 := by
      have : (N : ℚ) = (q : ℚ) * n := by rw [← hN, hn]
      have hN' : N = q * n := by exact_mod_cast this
      rw [hN']; push_cast; rw [CharP.cast_eq_zero F q, zero_mul]
    have h3 : cΛ ⟨x, hx⟩ * cΛ ⟨star x, hx'⟩ = 0 := by
      rw [← hc.mul' hx hx' (hΛo.mul_mem hx hx'), hc.congr (mul_star_eq_coe_nrd x) _ (by rw [hN]; exact intCast_mem hΛo N),
        hc.congr (by rw [hN]) _ (intCast_mem hΛo N), hc.map_intCast hΛo, hNq]
    rw [h2] at h3
    exact mul_self_eq_zero.1 h3

  obtain ⟨⟨-, -, ⟨x₀, hx₀Λ, hx₀P, hx₀nq⟩, -, hPP⟩, huniq⟩ :=
    IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq hB Λ hΛ q (Or.inl rfl)
  have hcx₀ : cΛ ⟨x₀, hx₀Λ⟩ = 0 := hkill x₀ hx₀Λ hx₀P

  let J : Submodule ℤ ℍ[ℚ, a, b] :=
  { carrier := {x | ∃ hx : x ∈ Λ, cΛ ⟨x, hx⟩ = 0}
    add_mem' := by
      rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
      exact ⟨Λ.add_mem hx hy, by rw [hc.add' hx hy, hx0, hy0, add_zero]⟩
    zero_mem' := ⟨Λ.zero_mem, hc.map_zero⟩
    smul_mem' := by
      rintro n x ⟨hx, hx0⟩
      refine ⟨Λ.smul_mem n hx, ?_⟩
      have := hc.map_zsmul n ⟨x, hx⟩
      rw [hx0, smul_zero] at this
      exact this }
  have hJmem : ∀ {x : ℍ[ℚ, a, b]}, x ∈ J ↔ ∃ hx : x ∈ Λ, cΛ ⟨x, hx⟩ = 0 := Iff.rfl
  have hJΛ : J ≤ Λ := fun x ⟨hx, _⟩ => hx
  have hqJ : ∀ y ∈ Λ, (q : ℤ) ⋇ y ∈ J := fun y hy => by
    refine ⟨Λ.smul_mem _ hy, ?_⟩
    have := hc.map_zsmul (q : ℤ) ⟨y, hy⟩
    rw [zsmul_eq_mul, hq0F, zero_mul] at this
    exact this
  have hJleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    rintro m hm x ⟨hx, hx0⟩
    exact ⟨hΛo.mul_mem hm hx, by rw [hc.mul' hm hx, hx0, mul_zero]⟩

  have hsplit : ∀ m ∈ Λ, ∃ (k : ℤ), m - ((k : ℚ) : ℍ[ℚ, a, b]) ∈ J := by
    intro m hm
    obtain ⟨k, hk⟩ := hint ⟨m, hm⟩
    refine ⟨k, Λ.sub_mem hm (intCast_mem hΛo k), ?_⟩
    rw [hc.sub' hm (intCast_mem hΛo k), hc.map_intCast hΛo, hk, sub_self]
  rcases huniq J hJΛ hqJ hJleft with hA | hBcase | hC
  ·
    exact hx₀nq ((hA x₀).1 ⟨hx₀Λ, hcx₀⟩)
  ·

    let J' : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {x | ∃ (k : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧ x = k ⋇ x₀ + (q : ℤ) ⋇ y}
      add_mem' := by
        rintro x x' ⟨k, y, hy, rfl⟩ ⟨k', y', hy', rfl⟩
        exact ⟨k + k', y + y', Λ.add_mem hy hy', by rw [add_smul, smul_add]; abel⟩
      zero_mem' := ⟨0, 0, Λ.zero_mem, by simp⟩
      smul_mem' := by
        rintro n x ⟨k, y, hy, rfl⟩
        exact ⟨n * k, n ⋇ y, Λ.smul_mem n hy, by rw [smul_add, mul_smul, smul_comm n (q : ℤ) y]⟩ }
    have hJ'mem : ∀ {x : ℍ[ℚ, a, b]}, x ∈ J' ↔ ∃ (k : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧ x = k ⋇ x₀ + (q : ℤ) ⋇ y :=
      Iff.rfl
    have hJ'Λ : J' ≤ Λ := by
      rintro x ⟨k, y, hy, rfl⟩
      exact Λ.add_mem (Λ.smul_mem k hx₀Λ) (Λ.smul_mem _ hy)
    have hqJ' : ∀ y ∈ Λ, (q : ℤ) ⋇ y ∈ J' := fun y hy => ⟨0, y, hy, by rw [zero_smul, zero_add]⟩
    have hx₀J' : x₀ ∈ J' := ⟨1, 0, Λ.zero_mem, by rw [one_smul, smul_zero, add_zero]⟩
    have hJ'left : ∀ m ∈ Λ, ∀ x ∈ J', m * x ∈ J' := by
      rintro m hm x ⟨k, y, hy, rfl⟩
      obtain ⟨k₁, hp⟩ := hsplit m hm
      set p := m - ((k₁ : ℚ) : ℍ[ℚ, a, b]) with hp_def
      have hpP : p ∈ Λ ∧ ∃ n : ℤ, nrd p = (q : ℚ) * n := (hBcase p).1 hp
      obtain ⟨z, hz, hpz⟩ := hPP p hpP.1 x₀ hx₀Λ hpP.2 hx₀P
      have hm' : m = ((k₁ : ℚ) : ℍ[ℚ, a, b]) + p := by rw [hp_def]; abel
      have hmx₀ : m * x₀ = k₁ ⋇ x₀ + (q : ℤ) ⋇ z := by
        rw [hm', add_mul, hpz]
        congr 1
        rw [zsmul_eq_mul]
        norm_cast
      refine ⟨k * k₁, k ⋇ z + m * y, Λ.add_mem (Λ.smul_mem k hz) (hΛo.mul_mem hm hy), ?_⟩
      rw [mul_add, mul_smul_comm, mul_smul_comm, hmx₀, smul_add, ← mul_smul, smul_comm k (q : ℤ) z,
        smul_add]
      abel
    rcases huniq J' hJ'Λ hqJ' hJ'left with hA' | hB' | hC'
    · exact hx₀nq ((hA' x₀).1 hx₀J')
    ·
      have hgen : ∀ m ∈ Λ, ∃ (k k' : ℤ) (y : ℍ[ℚ, a, b]), y ∈ Λ ∧
          m = ((k : ℚ) : ℍ[ℚ, a, b]) + k' ⋇ x₀ + (q : ℤ) ⋇ y := by
        intro m hm
        obtain ⟨k, hp⟩ := hsplit m hm
        obtain ⟨k', y, hy, hpy⟩ := (hB' _).2 ((hBcase _).1 hp)
        exact ⟨k, k', y, hy, by rw [add_assoc, ← hpy]; abel⟩
      have hle := relIndex_le_sq (q := q) Λ hΛo x₀ hx₀Λ hgen
      have h4 := IsOrder.relIndex_span_smul_eq_pow_four hΛo q (Fact.out : q.Prime).pos
      rw [h4] at hle
      have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
      have : q ^ 4 ≤ q ^ 2 := hle
      have : ¬ (q ^ 4 ≤ q ^ 2) := by
        rw [not_le]
        exact Nat.pow_lt_pow_right (by omega) (by norm_num)
      contradiction
    ·
      have h1 : (1 : ℍ[ℚ, a, b]) ∈ J' := by rw [hC']; exact hΛo.one_mem
      obtain ⟨k, y, hy, hky⟩ := h1
      have : cΛ ⟨1, hΛo.one_mem⟩ = 0 := by
        rw [hc.congr hky hΛo.one_mem (Λ.add_mem (Λ.smul_mem k hx₀Λ) (Λ.smul_mem _ hy)),
          hc.add' (Λ.smul_mem k hx₀Λ) (Λ.smul_mem _ hy)]
        have e1 : cΛ ⟨k ⋇ x₀, Λ.smul_mem k hx₀Λ⟩ = 0 := by
          have := hc.map_zsmul k ⟨x₀, hx₀Λ⟩
          rw [hcx₀, smul_zero] at this; exact this
        have e2 : cΛ ⟨(q : ℤ) ⋇ y, Λ.smul_mem _ hy⟩ = 0 := ((hJmem).1 (hqJ y hy)).2
        rw [e1, e2, add_zero]
      rw [hc.one] at this
      exact one_ne_zero this
  ·
    have h1 : (1 : ℍ[ℚ, a, b]) ∈ J := by rw [hC]; exact hΛo.one_mem
    obtain ⟨h1Λ, h10⟩ := h1
    rw [hc.one] at h10
    exact one_ne_zero h10

end ResidueLambda
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar"

section Transport

variable {A : Type*} [Ring A]

theorem transport_identity (g0 g1 a' b' c' d' v0 v1 : A) :
    g0 * (a' * v0 + b' * v1) + g1 * (c' * v0 + d' * v1) - (g0 * v0 + g1 * v1) * a' =
      g0 * (a' * v0 - v0 * a' + b' * v1) + g1 * (c' * v0 + (d' - a') * v1 + (a' * v1 - v1 * a')) := by
  noncomm_ring

theorem mulVec_two_apply (M : Matrix (Fin 2) (Fin 2) A) (v : Fin 2 → A) (i : Fin 2) :
    (M.mulVec v) i = M i 0 * v 0 + M i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_single_one_apply (M : Matrix (Fin 2) (Fin 2) A) (i l : Fin 2) :
    (M.mulVec (Pi.single l 1)) i = M i l := by
  rw [Matrix.mulVec_single_one]; rfl

end Transport
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar"

end P2mTypeFix
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix.IsChar P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt.P2mTypeFix"

open P2mTypeFix in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {c d : ℚ} (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsMaximalOrder O)
    (j₀ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj₀ : ∀ m ∈ Λ, ∀ i l : Fin 2, j₀ m i l ∈ O) :
    ∃ (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]),
      γ * γ' = 1 ∧ γ' * γ = 1 ∧ (∀ x : ℍ[ℚ, a, b], j x = γ' * j₀ x * γ) ∧
      ∃ (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O),
      ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
        (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F) := by
  classical
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.1
  have hOo : QuaternionAlgebra.IsOrder O := hO.1
  have hj₀' : ∀ (m : ↥Λ) (i l : Fin 2), j₀ (m : ℍ[ℚ, a, b]) i l ∈ O := fun m i l => hj₀ m m.2 i l
  by_cases hsp : ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F), IsChar O χ →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        (rho j₀ Λ O hj₀' χ m).trace = n
  ·
    refine ⟨j₀, 1, 1, one_mul 1, one_mul 1, fun x => by rw [one_mul, mul_one], hj₀', ?_⟩
    intro F _ _ χ h1 hadd hmul m n hn
    have := hsp F χ ⟨h1, hadd, hmul⟩ m n hn
    rwa [Matrix.trace_fin_two, rho_apply, rho_apply] at this

  push Not at hsp
  obtain ⟨F₀, instF, instC, χ₀, hχ₀, m₁, n₁, hn₁, hne⟩ := hsp
  have hsc₀ : ∀ m : ↥Λ, IsScalarShape (rho j₀ Λ O hj₀' χ₀ m) := by
    rcases dichotomy j₀ hΛo hOo hj₀' hχ₀ with h | h
    · exact absurd (h m₁ n₁ hn₁) hne
    · exact h

  set K := kerSub O χ₀ hχ₀ with hK
  have hKO : K ≤ O := kerSub_le O hχ₀
  have hKl : ∀ {o p : ℍ[ℚ, c, d]}, o ∈ O → p ∈ K → o * p ∈ K := fun ho hp =>
    mul_mem_kerSub_left O hχ₀ hOo ho hp
  have hKr : ∀ {o p : ℍ[ℚ, c, d]}, p ∈ K → o ∈ O → p * o ∈ K := fun hp ho =>
    mul_mem_kerSub_right O hχ₀ hOo hp ho
  have hKK : ∀ {p p' : ℍ[ℚ, c, d]}, p ∈ K → p' ∈ K → ∃ z ∈ O, p * p' = (q : ℤ) ⋇ z := fun hp hp' =>
    exists_mul_eq_zsmul q hH O hO hχ₀ hp hp'

  have h10 : ∀ m : ↥Λ, j₀ (m : ℍ[ℚ, a, b]) 1 0 ∈ K := fun m => ⟨hj₀' m 1 0, (hsc₀ m).2.1⟩
  have hdiag : ∀ m : ↥Λ, j₀ (m : ℍ[ℚ, a, b]) 0 0 - j₀ (m : ℍ[ℚ, a, b]) 1 1 ∈ K := fun m =>
    sub_mem_kerSub_of_apply_eq O hχ₀ _ _ (hsc₀ m).2.2

  let M₁ : Submodule ℤ (Fin 2 → ℍ[ℚ, c, d]) :=
  { carrier := {x | x 0 ∈ O ∧ x 1 ∈ K}
    add_mem' := fun {x y} hx hy => ⟨O.add_mem hx.1 hy.1, K.add_mem hx.2 hy.2⟩
    zero_mem' := ⟨O.zero_mem, K.zero_mem⟩
    smul_mem' := fun n x hx => ⟨O.smul_mem n hx.1, K.smul_mem n hx.2⟩ }
  have hM₁mem : ∀ {x : Fin 2 → ℍ[ℚ, c, d]}, x ∈ M₁ ↔ x 0 ∈ O ∧ x 1 ∈ K := Iff.rfl

  have hM₁O : ∀ x ∈ M₁, ∀ o ∈ O, (fun i => x i * o) ∈ M₁ := fun x hx o ho =>
    hM₁mem.2 ⟨hOo.mul_mem (hM₁mem.1 hx).1 ho, hKr (hM₁mem.1 hx).2 ho⟩

  have hM₁Λ : ∀ x ∈ M₁, ∀ m : ↥Λ, (j₀ (m : ℍ[ℚ, a, b])).mulVec x ∈ M₁ := by
    intro x hx m
    obtain ⟨hx0, hx1⟩ := hM₁mem.1 hx
    refine hM₁mem.2 ⟨?_, ?_⟩
    · rw [mulVec_two_apply]
      exact O.add_mem (hOo.mul_mem (hj₀' m 0 0) hx0) (hOo.mul_mem (hj₀' m 0 1) (hKO hx1))
    · rw [mulVec_two_apply]
      exact K.add_mem (hKr (h10 m) hx0) (hKl (hj₀' m 1 1) hx1)

  have hfg : M₁.FG := by
    have hT : (Submodule.pi Set.univ (fun _ : Fin 2 => O)).FG := Submodule.fg_pi (fun _ => hOo.fg)
    refine Submodule.FG.of_le hT ?_
    intro x hx i _
    obtain ⟨hx0, hx1⟩ := hM₁mem.1 hx
    fin_cases i
    · exact hx0
    · exact hKO hx1

  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hspan : Submodule.span ℚ (M₁ : Set (Fin 2 → ℍ[ℚ, c, d])) = ⊤ := by
    refine top_unique fun x _ => ?_
    have hx : x = ∑ k : Fin 2, Pi.single k (x k) := by
      funext i
      rw [Finset.sum_apply, Fin.sum_univ_two]
      fin_cases i <;> simp
    rw [hx]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hxk : x k ∈ Submodule.span ℚ (O : Set ℍ[ℚ, c, d]) := by rw [hOo.spanTop]; trivial
    generalize x k = y at hxk
    induction hxk using Submodule.span_induction with
    | mem o ho =>
      have hmem : Pi.single k ((q : ℤ) ⋇ o) ∈ M₁ := by
        refine hM₁mem.2 ⟨?_, ?_⟩
        · by_cases hk : (0 : Fin 2) = k
          · subst hk; rw [Pi.single_eq_same]; exact O.smul_mem _ ho
          · rw [Pi.single_eq_of_ne hk]; exact O.zero_mem
        · by_cases hk : (1 : Fin 2) = k
          · subst hk; rw [Pi.single_eq_same]; exact zsmul_mem_kerSub q O hχ₀ hOo ho
          · rw [Pi.single_eq_of_ne hk]; exact K.zero_mem
      have : (Pi.single k o : Fin 2 → ℍ[ℚ, c, d]) = (q : ℚ)⁻¹ ⋇ (Pi.single k ((q : ℤ) ⋇ o) : Fin 2 → ℍ[ℚ, c, d]) := by
        rw [← Pi.single_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hq0,
          one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [Pi.single_add]; exact Submodule.add_mem _ hu hw
    | smul r u _ hu => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hu

  obtain ⟨γ, γ', hγγ', hγ'γ, hmem⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem q hH O hO M₁ hfg hspan hM₁O

  let j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] := (conjAlgHom (R := ℚ) γ γ' hγγ' hγ'γ).comp j₀
  have hj_apply : ∀ x, j x = γ' * j₀ x * γ := fun x => rfl
  have hcol : ∀ l : Fin 2, γ.mulVec (Pi.single l 1) ∈ M₁ := by
    intro l
    rw [hmem, Matrix.mulVec_mulVec, hγ'γ, Matrix.one_mulVec]
    intro i
    by_cases hil : i = l
    · subst hil; rw [Pi.single_eq_same]; exact hOo.one_mem
    · rw [Pi.single_eq_of_ne hil]; exact O.zero_mem
  have hγ0 : ∀ l : Fin 2, γ 0 l ∈ O := fun l => by
    rw [← mulVec_single_one_apply γ 0 l]; exact (hM₁mem.1 (hcol l)).1
  have hγ1 : ∀ l : Fin 2, γ 1 l ∈ K := fun l => by
    rw [← mulVec_single_one_apply γ 1 l]; exact (hM₁mem.1 (hcol l)).2
  have hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O := by
    intro m i l
    rw [hj_apply, mul_mul_apply_eq_mulVec]
    exact (hmem _).1 (hM₁Λ _ (hcol l) m) i
  refine ⟨j, γ, γ', hγγ', hγ'γ, hj_apply, hj, ?_⟩
  intro F _ _ χ h1 hadd hmul m n hn
  have hχ : IsChar O χ := ⟨h1, hadd, hmul⟩
  rcases dichotomy j hΛo hOo hj hχ with hgood | hbad
  · have := hgood m n hn
    rwa [Matrix.trace_fin_two, rho_apply, rho_apply] at this
  exfalso

  have hKχ : ∀ {x : ℍ[ℚ, c, d]} (hx : x ∈ O), χ ⟨x, hx⟩ = 0 ↔ x ∈ K := fun hx =>
    apply_eq_zero_iff_mem_kerSub q hH O hO hχ₀ hχ hx

  have hb' : ∀ μ : ↥Λ, j (μ : ℍ[ℚ, a, b]) 0 1 ∈ K := fun μ => (hKχ (hj μ 0 1)).1 (hbad μ).1
  have hc' : ∀ μ : ↥Λ, j (μ : ℍ[ℚ, a, b]) 1 0 ∈ K := fun μ => (hKχ (hj μ 1 0)).1 (hbad μ).2.1
  have hd' : ∀ μ : ↥Λ, j (μ : ℍ[ℚ, a, b]) 1 1 - j (μ : ℍ[ℚ, a, b]) 0 0 ∈ K := fun μ => by
    obtain ⟨hx, hx0⟩ := sub_mem_kerSub_of_apply_eq O hχ (hj μ 1 1) (hj μ 0 0) (hbad μ).2.2.symm
    exact (hKχ hx).1 hx0

  have hcomm : ∀ {x y : ℍ[ℚ, c, d]}, x ∈ O → y ∈ O → x * y - y * x ∈ K := fun {x y} hx hy => by
    refine (hKχ (O.sub_mem (hOo.mul_mem hx hy) (hOo.mul_mem hy hx))).1 ?_
    rw [hχ.sub' (hOo.mul_mem hx hy) (hOo.mul_mem hy hx), hχ.mul' hx hy, hχ.mul' hy hx, mul_comm, sub_self]

  have transport : ∀ (μ : ↥Λ) (w : Fin 2 → ℍ[ℚ, c, d]), w ∈ M₁ →
      ((j₀ (μ : ℍ[ℚ, a, b])).mulVec w 0 - w 0 * j (μ : ℍ[ℚ, a, b]) 0 0 ∈ K) ∧
      ∃ z ∈ O, (j₀ (μ : ℍ[ℚ, a, b])).mulVec w 1 - w 1 * j (μ : ℍ[ℚ, a, b]) 0 0 = (q : ℤ) ⋇ z := by
    intro μ w hw
    set v : Fin 2 → ℍ[ℚ, c, d] := γ'.mulVec w with hv
    have hvO : ∀ i, v i ∈ O := (hmem w).1 hw
    have hwv : w = γ.mulVec v := by rw [hv, Matrix.mulVec_mulVec, hγγ', Matrix.one_mulVec]
    have hjw : (j₀ (μ : ℍ[ℚ, a, b])).mulVec w = γ.mulVec ((j (μ : ℍ[ℚ, a, b])).mulVec v) := by
      rw [Matrix.mulVec_mulVec, hj_apply, ← mul_assoc, ← mul_assoc, hγγ', one_mul, ← Matrix.mulVec_mulVec,
        ← hwv]
    have hp0K : j (μ : ℍ[ℚ, a, b]) 0 0 * v 0 - v 0 * j (μ : ℍ[ℚ, a, b]) 0 0 + j (μ : ℍ[ℚ, a, b]) 0 1 * v 1 ∈ K :=
      K.add_mem (hcomm (hj μ 0 0) (hvO 0)) (hKr (hb' μ) (hvO 1))
    have hp1K : j (μ : ℍ[ℚ, a, b]) 1 0 * v 0 + (j (μ : ℍ[ℚ, a, b]) 1 1 - j (μ : ℍ[ℚ, a, b]) 0 0) * v 1 +
        (j (μ : ℍ[ℚ, a, b]) 0 0 * v 1 - v 1 * j (μ : ℍ[ℚ, a, b]) 0 0) ∈ K :=
      K.add_mem (K.add_mem (hKr (hc' μ) (hvO 0)) (hKr (hd' μ) (hvO 1))) (hcomm (hj μ 0 0) (hvO 1))
    have key : ∀ i, (j₀ (μ : ℍ[ℚ, a, b])).mulVec w i - w i * j (μ : ℍ[ℚ, a, b]) 0 0 =
        γ i 0 * (j (μ : ℍ[ℚ, a, b]) 0 0 * v 0 - v 0 * j (μ : ℍ[ℚ, a, b]) 0 0 + j (μ : ℍ[ℚ, a, b]) 0 1 * v 1) +
        γ i 1 * (j (μ : ℍ[ℚ, a, b]) 1 0 * v 0 + (j (μ : ℍ[ℚ, a, b]) 1 1 - j (μ : ℍ[ℚ, a, b]) 0 0) * v 1 +
          (j (μ : ℍ[ℚ, a, b]) 0 0 * v 1 - v 1 * j (μ : ℍ[ℚ, a, b]) 0 0)) := by
      intro i
      rw [hjw, mulVec_two_apply, mulVec_two_apply, mulVec_two_apply]
      conv_lhs => rw [hwv, mulVec_two_apply]
      exact transport_identity _ _ _ _ _ _ _ _
    refine ⟨?_, ?_⟩
    · rw [key]; exact K.add_mem (hKl (hγ0 0) hp0K) (hKl (hγ0 1) hp1K)
    · obtain ⟨z₁, hz₁, e₁⟩ := hKK (hγ1 0) hp0K
      obtain ⟨z₂, hz₂, e₂⟩ := hKK (hγ1 1) hp1K
      exact ⟨z₁ + z₂, O.add_mem hz₁ hz₂, by rw [key, e₁, e₂, smul_add]⟩

  have hcommq : ∀ (μ : ↥Λ) (p : ℍ[ℚ, c, d]), p ∈ K →
      ∃ z ∈ O, j₀ (μ : ℍ[ℚ, a, b]) 0 0 * p - p * j₀ (μ : ℍ[ℚ, a, b]) 0 0 = (q : ℤ) ⋇ z := by
    intro μ p hp

    have he₀ : (Pi.single 0 1 : Fin 2 → ℍ[ℚ, c, d]) ∈ M₁ :=
      hM₁mem.2 ⟨by rw [Pi.single_eq_same]; exact hOo.one_mem,
        by rw [Pi.single_eq_of_ne (by decide)]; exact K.zero_mem⟩
    have h1 := (transport μ _ he₀).1
    rw [mulVec_single_one_apply, Pi.single_eq_same, one_mul] at h1

    have hep : (Pi.single 1 p : Fin 2 → ℍ[ℚ, c, d]) ∈ M₁ :=
      hM₁mem.2 ⟨by rw [Pi.single_eq_of_ne (by decide)]; exact O.zero_mem, by rw [Pi.single_eq_same]; exact hp⟩
    obtain ⟨z, hz, h2⟩ := (transport μ _ hep).2
    rw [mulVec_two_apply, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), Pi.single_eq_same, mul_zero,
      zero_add] at h2

    have hδα : j₀ (μ : ℍ[ℚ, a, b]) 1 1 - j₀ (μ : ℍ[ℚ, a, b]) 0 0 ∈ K := by
      rw [← neg_sub]; exact K.neg_mem (hdiag μ)
    have ha'α : j (μ : ℍ[ℚ, a, b]) 0 0 - j₀ (μ : ℍ[ℚ, a, b]) 0 0 ∈ K := by
      rw [← neg_sub]; exact K.neg_mem h1
    obtain ⟨z', hz', h3⟩ := hKK hδα hp
    obtain ⟨z'', hz'', h4⟩ := hKK hp ha'α
    refine ⟨z - z' + z'', O.add_mem (O.sub_mem hz hz') hz'', ?_⟩
    calc j₀ (μ : ℍ[ℚ, a, b]) 0 0 * p - p * j₀ (μ : ℍ[ℚ, a, b]) 0 0
        = (j₀ (μ : ℍ[ℚ, a, b]) 1 1 * p - p * j (μ : ℍ[ℚ, a, b]) 0 0)
          - (j₀ (μ : ℍ[ℚ, a, b]) 1 1 - j₀ (μ : ℍ[ℚ, a, b]) 0 0) * p
          + p * (j (μ : ℍ[ℚ, a, b]) 0 0 - j₀ (μ : ℍ[ℚ, a, b]) 0 0) := by noncomm_ring
      _ = (q : ℤ) ⋇ z - (q : ℤ) ⋇ z' + (q : ℤ) ⋇ z'' := by rw [h2, h3, h4]
      _ = (q : ℤ) ⋇ (z - z' + z'') := by rw [smul_add, smul_sub]

  have hcΛ : IsChar Λ (fun μ : ↥Λ => χ ⟨j₀ (μ : ℍ[ℚ, a, b]) 0 0, hj₀' μ 0 0⟩) := by
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have e : j₀ ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 0 0 = 1 := by simp
      show χ ⟨j₀ ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 0 0, hj₀' _ 0 0⟩ = 1
      rw [hχ.congr e (hj₀' _ 0 0) hOo.one_mem]; exact hχ.one hOo.one_mem
    · intro x y
      have e : j₀ ((x + y : ↥Λ) : ℍ[ℚ, a, b]) 0 0 = j₀ (x : ℍ[ℚ, a, b]) 0 0 + j₀ (y : ℍ[ℚ, a, b]) 0 0 := by
        simp
      show χ ⟨j₀ ((x + y : ↥Λ) : ℍ[ℚ, a, b]) 0 0, hj₀' _ 0 0⟩ =
        χ ⟨j₀ (x : ℍ[ℚ, a, b]) 0 0, hj₀' x 0 0⟩ + χ ⟨j₀ (y : ℍ[ℚ, a, b]) 0 0, hj₀' y 0 0⟩
      rw [hχ.congr e (hj₀' _ 0 0) (O.add_mem (hj₀' x 0 0) (hj₀' y 0 0)), hχ.add']
    · intro x y h
      have e : j₀ ((⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 0 0 =
          j₀ (x : ℍ[ℚ, a, b]) 0 0 * j₀ (y : ℍ[ℚ, a, b]) 0 0 + j₀ (x : ℍ[ℚ, a, b]) 0 1 * j₀ (y : ℍ[ℚ, a, b]) 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have hm00 := hOo.mul_mem (hj₀' x 0 0) (hj₀' y 0 0)
      have hm01 := hOo.mul_mem (hj₀' x 0 1) (hj₀' y 1 0)
      show χ ⟨j₀ ((⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 0 0, hj₀' _ 0 0⟩ =
        χ ⟨j₀ (x : ℍ[ℚ, a, b]) 0 0, hj₀' x 0 0⟩ * χ ⟨j₀ (y : ℍ[ℚ, a, b]) 0 0, hj₀' y 0 0⟩
      rw [hχ.congr e (hj₀' _ 0 0) (O.add_mem hm00 hm01), hχ.add' hm00 hm01, hχ.mul' (hj₀' x 0 0) (hj₀' y 0 0),
        hχ.mul' (hj₀' x 0 1) (hj₀' y 1 0)]
      have : χ ⟨j₀ (y : ℍ[ℚ, a, b]) 1 0, hj₀' y 1 0⟩ = 0 := (hKχ (hj₀' y 1 0)).2 (h10 y)
      rw [this, mul_zero, add_zero]
  obtain ⟨μ, hμ⟩ := exists_pow_ne hB Λ hΛ _ hcΛ
  have hαO : j₀ (μ : ℍ[ℚ, a, b]) 0 0 ∈ O := hj₀' μ 0 0
  have hαs : star (j₀ (μ : ℍ[ℚ, a, b]) 0 0) ∈ O := star_mem_of_isOrder hOo hαO

  have huO : j₀ (μ : ℍ[ℚ, a, b]) 0 0 - star (j₀ (μ : ℍ[ℚ, a, b]) 0 0) ∈ O := O.sub_mem hαO hαs
  have huK : j₀ (μ : ℍ[ℚ, a, b]) 0 0 - star (j₀ (μ : ℍ[ℚ, a, b]) 0 0) ∉ K := by
    intro hu
    have h0 := (hKχ huO).2 hu
    rw [hχ.sub' hαO hαs, apply_star q hH O hO hχ hαO hαs, sub_eq_zero] at h0
    exact hμ h0.symm

  obtain ⟨h, hhK, hhv⟩ := exists_mem_kerSub_padicValRat_eq_one q hH O hO hχ₀

  obtain ⟨z₁, hz₁, e₁⟩ := hcommq μ h hhK
  obtain ⟨z₂, hz₂, e₂⟩ := exists_twist q hH O hO hχ₀ hαO hhK
  have e : h * (j₀ (μ : ℍ[ℚ, a, b]) 0 0 - star (j₀ (μ : ℍ[ℚ, a, b]) 0 0)) = (q : ℤ) ⋇ (z₂ - z₁) := by
    rw [smul_sub, ← e₁, ← e₂]; noncomm_ring
  exact not_dvd_unif_mul q hH O hO hχ₀ (hKO hhK) hhv huO huK (O.sub_mem hz₂ hz₁) e

end S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt (solution)
