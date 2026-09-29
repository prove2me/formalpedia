-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5bdcad3d-e75d-554b-9662-b1513fee0a85

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring
import Theorems.Thm_QuaternionAlgebra_relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

namespace LocalType

section Generic
variable {K : Type*} [Field K] (O : ValuationSubring K)

def IsInt (M : Matrix (Fin 2) (Fin 2) K) : Prop := ∀ i j, M i j ∈ O

theorem IsInt.mul {M N : Matrix (Fin 2) (Fin 2) K} (hM : IsInt O M) (hN : IsInt O N) : IsInt O (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.toSubring.sum_mem fun k _ => O.toSubring.mul_mem (hM i k) (hN k j)

theorem IsInt.one : IsInt O (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]

theorem isInt_conj_iff (k : GL (Fin 2) K) (hk : IsInt O (k : Matrix (Fin 2) (Fin 2) K))
    (hki : IsInt O ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt O (((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y * (k : Matrix (Fin 2) (Fin 2) K)) ↔ IsInt O Y := by
  constructor
  · intro h
    have e : Y = (k : Matrix (Fin 2) (Fin 2) K) *
        ((((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y * (k : Matrix (Fin 2) (Fin 2) K))) *
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [e]
    exact IsInt.mul O (IsInt.mul O hk h) hki
  · intro h
    exact IsInt.mul O (IsInt.mul O hki h) hk

theorem isInt_conj_iff' (k : GL (Fin 2) K) (hk : IsInt O (k : Matrix (Fin 2) (Fin 2) K))
    (hki : IsInt O ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt O ((k : Matrix (Fin 2) (Fin 2) K) * Y * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ↔ IsInt O Y := by
  have h := isInt_conj_iff O k⁻¹ hki (by rw [inv_inv]; exact hk) Y
  rw [inv_inv] at h
  exact h

def mkGL (M M' : Matrix (Fin 2) (Fin 2) K) (h1 : M * M' = 1) (h2 : M' * M = 1) : GL (Fin 2) K := ⟨M, M', h1, h2⟩

theorem exists_GL (M M' : Matrix (Fin 2) (Fin 2) K) (h1 : M * M' = 1) (h2 : M' * M = 1) :
    ∃ g : GL (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) = M ∧ ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = M' :=
  ⟨mkGL M M' h1 h2, rfl, rfl⟩

theorem assoc4 (S A B C : Matrix (Fin 2) (Fin 2) K) : S * (A * B * C) = S * A * B * C := by noncomm_ring

theorem conj_decomp (s : K) (hs : s ≠ 0) (A A' B B' C C' Y : Matrix (Fin 2) (Fin 2) K) :
    C' * (B' * (A' * Matrix.scalar (Fin 2) s⁻¹)) * Y * (Matrix.scalar (Fin 2) s * A * B * C) =
      C' * (B' * A' * Y * (A * B)) * C := by
  have ecomm : Matrix.scalar (Fin 2) s⁻¹ * Y = Y * Matrix.scalar (Fin 2) s⁻¹ :=
    (Matrix.scalar_commute s⁻¹ (Commute.all s⁻¹) Y).eq
  have hS2 : Matrix.scalar (Fin 2) s⁻¹ * Matrix.scalar (Fin 2) s = (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_mul, inv_mul_cancel₀ hs, map_one]
  calc C' * (B' * (A' * Matrix.scalar (Fin 2) s⁻¹)) * Y * (Matrix.scalar (Fin 2) s * A * B * C)
      = C' * B' * A' * (Matrix.scalar (Fin 2) s⁻¹ * Y) * (Matrix.scalar (Fin 2) s * A * B * C) := by noncomm_ring
    _ = C' * B' * A' * (Y * Matrix.scalar (Fin 2) s⁻¹) * (Matrix.scalar (Fin 2) s * A * B * C) := by rw [ecomm]
    _ = C' * B' * A' * Y * (Matrix.scalar (Fin 2) s⁻¹ * Matrix.scalar (Fin 2) s) * A * B * C := by noncomm_ring
    _ = C' * (B' * A' * Y * (A * B)) * C := by rw [hS2]; noncomm_ring

theorem smul_eq_scalar_mul (s : K) (X : Matrix (Fin 2) (Fin 2) K) : s • X = Matrix.scalar (Fin 2) s * X := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]

theorem scalar_mul_eq_mul_scalar (s : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix.scalar (Fin 2) s * X = X * Matrix.scalar (Fin 2) s :=
  (Matrix.scalar_commute s (Commute.all s) X).eq

theorem scalar_conj (r : K) (P X Q : Matrix (Fin 2) (Fin 2) K) :
    P * (Matrix.scalar (Fin 2) r * X) * Q = Matrix.scalar (Fin 2) r * (P * X * Q) := by
  have e : Matrix.scalar (Fin 2) r * P = P * Matrix.scalar (Fin 2) r := (Matrix.scalar_commute r (Commute.all r) P).eq
  calc P * (Matrix.scalar (Fin 2) r * X) * Q = (P * Matrix.scalar (Fin 2) r) * X * Q := by noncomm_ring
    _ = (Matrix.scalar (Fin 2) r * P) * X * Q := by rw [e]
    _ = Matrix.scalar (Fin 2) r * (P * X * Q) := by noncomm_ring

theorem scalar_mul_apply (r : K) (A : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (Matrix.scalar (Fin 2) r * A) i j = r * A i j := by
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem smul_one_eq_scalar (r : K) : r • (1 : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) r := by
  rw [smul_eq_scalar_mul, Matrix.mul_one]

theorem isInt_scalar {r : K} (hr : r ∈ O) : IsInt O (Matrix.scalar (Fin 2) r) := by
  intro i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hr
  · exact O.zero_mem

theorem isInt_diagonal {x y : K} (hx : x ∈ O) (hy : y ∈ O) : IsInt O (Matrix.diagonal ![x, y]) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hx, hy, O.zero_mem]

theorem diag_mul_diag (x y : K) :
    Matrix.diagonal ![(1 : K), x] * Matrix.diagonal ![(1 : K), y] = Matrix.diagonal ![(1 : K), x * y] := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i; fin_cases i <;> simp

def conjEquiv (g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K ≃+* Matrix (Fin 2) (Fin 2) K where
  toFun x := ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K)
  invFun x := (g : Matrix (Fin 2) (Fin 2) K) * x * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  left_inv x := by
    show (g : Matrix (Fin 2) (Fin 2) K) * (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x *
      (g : Matrix (Fin 2) (Fin 2) K)) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv x := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((g : Matrix (Fin 2) (Fin 2) K) * x *
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * (g : Matrix (Fin 2) (Fin 2) K) = x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  map_mul' x y := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x * y) * (g : Matrix (Fin 2) (Fin 2) K) =
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K) *
        (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * y * (g : Matrix (Fin 2) (Fin 2) K))
    have hg : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x * y) * (g : Matrix (Fin 2) (Fin 2) K)
        = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * 1 * y * (g : Matrix (Fin 2) (Fin 2) K) := by noncomm_ring
      _ = _ := by rw [← hg]; noncomm_ring
  map_add' x y := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x + y) * (g : Matrix (Fin 2) (Fin 2) K) =
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K) +
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * y * (g : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.mul_add, Matrix.add_mul]

theorem conjEquiv_apply (g : GL (Fin 2) K) (x : Matrix (Fin 2) (Fin 2) K) :
    conjEquiv g x = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K) := rfl

end Generic

theorem natGenerator_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = ℓ := by
  show Rat.HeightOneSpectrum.natGenerator v = ℓ
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ ℓ := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hdvd

theorem exists_unit_mul_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (t₀ : v.adicCompletion ℚ) (ht₀ : t₀ ∈ v.adicCompletionIntegers ℚ) (ht₀0 : t₀ ≠ 0) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      t₀ = ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n := by
  set t : v.adicCompletionIntegers ℚ := ⟨t₀, ht₀⟩ with htdef
  have ht : t ≠ 0 := fun h => ht₀0 (by rw [htdef] at h; exact congrArg Subtype.val h)
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  set ψ := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v with hψ
  have ht' : ψ t ≠ 0 := fun h => ht (by simpa using congrArg ψ.symm h)
  refine ⟨(ψ t).valuation, Units.map ψ.symm.toRingEquiv.toRingHom.toMonoidHom (PadicInt.unitCoeff ht'), ?_⟩
  show (t : v.adicCompletion ℚ) = _
  have key : t = ψ.symm ((PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) *
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) ^ (ψ t).valuation) := by
    rw [← PadicInt.unitCoeff_spec ht']; simp
  have hp : (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      ((ℓ : ℕ) : v.adicCompletion ℚ) := by
    rw [← natGenerator_eq hℓ v hv]; exact map_natCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) _
  have e1 : (t : v.adicCompletion ℚ) =
      ((ψ.symm (PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) *
        (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ^ (ψ t).valuation := by
    conv_lhs => rw [key]
    rw [map_mul, map_pow, map_natCast]
    push_cast
    rfl
  rw [e1, hp]
  rfl

end LocalType

namespace LocalType

variable {a b : ℚ}

theorem natGenerator_dvd_iff' (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator v ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  (natGenerator_dvd_iff' v _).mp dvd_rfl

theorem exists_splitting (hab : a ≠ 0 ∧ b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hnd
  push Not at hnd
  obtain ⟨x₀, x₁, x₂, x₃, h0, hx⟩ := hnd
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hab.1
  have hb : (b : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hab.2
  have hx' : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) := fun h => hx h.1 h.2.1 h.2.2.1 h.2.2.2
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero (v.adicCompletion ℚ) two_ne_zero
    (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ) ha hb x₀ x₁ x₂ x₃ hx' h0
  obtain ⟨φ, hφ, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := (a : v.adicCompletion ℚ)) (d₂ := (0 : v.adicCompletion ℚ)) (d₃ := (b : v.adicCompletion ℚ))
    (eq_ratCast _ a) (by simp) (eq_ratCast _ b) ψ
  exact ⟨φ, hφ⟩

theorem exists_standard_frame (hab : a ≠ 0 ∧ b ≠ 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        z ∈ Submodule.localBox Λ v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨φ₀, hφ₀⟩ := exists_splitting hab v hnd
  obtain ⟨g, hg⟩ := hΛ.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers v φ₀ hφ₀
  refine ⟨φ₀.trans (conjEquiv g), fun r => ?_, fun z => ?_⟩
  · rw [RingEquiv.trans_apply, conjEquiv_apply, hφ₀, smul_one_eq_scalar, ← scalar_mul_eq_mul_scalar, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  · rw [hg z]; rfl

theorem one_tmul_mul_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  unfold Submodule.localBox at hx ⊢
  have hle : AddSubgroup.closure {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ |
        ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c} ≤
      (AddSubgroup.closure {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ |
        ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}).comap
        (AddMonoidHom.mulLeft ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z, hz, d, hd, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
    refine AddSubgroup.subset_closure ⟨z, hz, c * d, mul_mem hc hd, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hx

theorem inv_natCast_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ((n : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((n : ℕ) : 𝓞 ℚ) := by
    rw [map_natCast]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((n : ℕ) : 𝓞 ℚ)
  erw [h2, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).mpr hnv, inv_one]

theorem nsmul_mem_of_relIndex_eq {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (hN : (Λ₁ ⊓ Λ₂).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) :
    ∀ z ∈ Λ₁, ((N : ℕ) : ℤ) • z ∈ Λ₂ := by
  intro z hz
  have h := AddSubgroup.nsmul_index_mem ((Λ₁ ⊓ Λ₂).toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup) ⟨z, hz⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h
  change ((Λ₁ ⊓ Λ₂).toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup).index = N at hN
  rw [hN] at h
  have h' : N • z ∈ Λ₁ ⊓ Λ₂ := h
  rw [natCast_zsmul]
  exact h'.2

theorem localBox_le_of_nsmul_mem {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hN0 : N ≠ 0)
    (hN : ∀ z ∈ Λ, ((N : ℕ) : ℤ) • z ∈ Λ') (v : HeightOneSpectrum (𝓞 ℚ))
    (hNv : ((N : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  have hNK : ((N : v.adicCompletion ℚ)) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by exact_mod_cast hN0)
  have key : z ⊗ₜ[ℚ] c = (((N : ℕ) : ℤ) • z) ⊗ₜ[ℚ] (((N : v.adicCompletion ℚ))⁻¹ * c) := by
    rw [TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast, ← mul_assoc, mul_inv_cancel₀ hNK, one_mul]
  rw [key]
  exact AddSubgroup.subset_closure ⟨((N : ℕ) : ℤ) • z, hN z hz, _, mul_mem hNv hc, rfl⟩

theorem natCast_eq_one_tmul (v : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ) :
    ((N : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : v.adicCompletion ℚ) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, ih, Algebra.TensorProduct.one_def, TensorProduct.tmul_add]

theorem natCast_rat_smul_eq (v : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ) (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ((N : ℕ) : ℚ) • y = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : v.adicCompletion ℚ)) * y := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, natCast_eq_one_tmul]

theorem eq_factorization_of_prod_pow_natGenerator_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (n : HeightOneSpectrum (𝓞 ℚ) → ℕ) (N : ℕ)
    (h : ∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v) ^ (n v) = N) (v₀ : HeightOneSpectrum (𝓞 ℚ)) (hv₀ : v₀ ∈ S) :
    n v₀ = N.factorization (Rat.HeightOneSpectrum.natGenerator v₀) := by
  classical
  have hne : ∀ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v) ^ (n v) ≠ 0 :=
    fun v _ => pow_ne_zero _ (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero
  rw [← h, Nat.factorization_prod hne, Finset.sum_apply']
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have key : ∀ v ∈ S, n v * (Rat.HeightOneSpectrum.natGenerator v).factorization (Rat.HeightOneSpectrum.natGenerator v₀) =
      if v = v₀ then n v₀ else 0 := by
    intro v _
    rw [(Rat.HeightOneSpectrum.prime_natGenerator v).factorization, Finsupp.single_apply]
    by_cases hv : v = v₀
    · subst hv; simp
    · have hne' : Rat.HeightOneSpectrum.natGenerator v ≠ Rat.HeightOneSpectrum.natGenerator v₀ := by
        intro heq
        apply hv
        apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
        exact Subtype.ext heq
      rw [if_neg hne', if_neg hv, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' S v₀, if_pos hv₀]

end LocalType

namespace LocalType
section Generic2
variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem cancel_conj (s : K) (A A' B W W' : Matrix (Fin 2) (Fin 2) K) (hA : A' * A = 1) (hW : W * W' = 1) :
    A' * (Matrix.scalar (Fin 2) s * (A * B * W)) * W' = Matrix.scalar (Fin 2) s * B := by
  rw [scalar_conj]
  congr 1
  calc A' * (A * B * W) * W' = (A' * A) * B * (W * W') := by noncomm_ring
    _ = B := by rw [hA, hW, Matrix.one_mul, Matrix.mul_one]

theorem diag_entry_00 (x : K) : (Matrix.diagonal ![(1 : K), x]) 0 0 = 1 := by simp
theorem diag_entry_11 (x : K) : (Matrix.diagonal ![(1 : K), x]) 1 1 = x := by simp

end Generic2
end LocalType

namespace LocalType
section Generic3
variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem assoc5 (S A D U C : Matrix (Fin 2) (Fin 2) K) : S * (A * (D * U) * C) = S * A * D * (U * C) := by noncomm_ring

theorem assoc_conj (B' A' Y A B : Matrix (Fin 2) (Fin 2) K) : B' * A' * Y * (A * B) = B' * A' * Y * A * B := by noncomm_ring

theorem entry00_scalar_diag (s x : K) : (Matrix.scalar (Fin 2) s * Matrix.diagonal ![(1 : K), x]) 0 0 = s := by
  rw [scalar_mul_apply]; simp

theorem entry11_scalar_diag_scalar (r x s : K) :
    (Matrix.scalar (Fin 2) r * Matrix.diagonal ![(1 : K), x] * Matrix.scalar (Fin 2) s) 1 1 = r * x * s := by
  rw [Matrix.mul_assoc, scalar_mul_apply, ← scalar_mul_eq_mul_scalar, scalar_mul_apply]; simp; ring

theorem scalar_mul_scalar_inv (s : K) (hs : s ≠ 0) :
    Matrix.scalar (Fin 2) s * Matrix.scalar (Fin 2) s⁻¹ = (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← map_mul, mul_inv_cancel₀ hs, map_one]

theorem scalar_inv_mul_scalar (s : K) (hs : s ≠ 0) :
    Matrix.scalar (Fin 2) s⁻¹ * Matrix.scalar (Fin 2) s = (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← map_mul, inv_mul_cancel₀ hs, map_one]

theorem diag_mul_diag_inv' (x : K) (hx : x ≠ 0) :
    Matrix.diagonal ![(1 : K), x] * Matrix.diagonal ![(1 : K), x⁻¹] = 1 := by
  rw [diag_mul_diag, mul_inv_cancel₀ hx]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem diag_inv_mul_diag' (x : K) (hx : x ≠ 0) :
    Matrix.diagonal ![(1 : K), x⁻¹] * Matrix.diagonal ![(1 : K), x] = 1 := by
  rw [diag_mul_diag, inv_mul_cancel₀ hx]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem comm_of_val_eq_scalar (S g : GL (Fin 2) K) (s : K) (hS : (S : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) s) :
    S * g = g * S := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hS, scalar_mul_eq_mul_scalar]

end Generic3
end LocalType

open LocalType in
set_option maxHeartbeats 1600000 in
theorem solution
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈
      Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈
      Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
        Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m ∈ Submodule.localBoxUnits Λ₁ v) ∧
    ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ), ℓ.Prime → ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ℓ ∣ N →
      (¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ∧
      ∃ (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)),
        (∀ r : v.adicCompletion ℚ,
          φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
        (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
          z ∈ Submodule.localBox Λ₁ v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ) ∧
        ∃ k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ),
          (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
            v.adicCompletionIntegers ℚ) ∧
          (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
            v.adicCompletionIntegers ℚ) ∧
          φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
            (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
              Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (padicValNat ℓ N)] *
              (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  classical
  have h1o : IsOrder Λ₁ := hΛ₁.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  have hΛ₂ : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m) := hΛ₁.conjByFiniteIdele m
  have h2o : IsOrder (Submodule.conjByFiniteIdele Λ₁ m) := hΛ₂.isOrder
  have hRo : IsOrder (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m) := h1o.inf h2o

  have hm₁v : ∀ v, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.localBox Λ₁ v :=
    (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ h1o.fg h1o.spanTop _).mp hm₁
  have hmNv : ∀ v, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : v.adicCompletion ℚ)) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ₁ v := by
    intro v
    have h := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ h1o.fg h1o.spanTop _).mp hmN v
    rwa [map_smul, natCast_rat_smul_eq] at h

  have hmv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ mv : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      mv = Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m ∧
      (mv : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∧
      ((mv⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    fun v => ⟨_, rfl, rfl, Units.coe_map_inv _ _⟩
  choose mv hmvdef hmvval hmvinv using hmv
  refine ⟨?_, ?_⟩
  ·
    intro v hNv
    rw [Submodule.mem_localBoxUnits_iff, ← hmvdef, hmvval, hmvinv]
    refine ⟨hm₁v v, ?_⟩
    have hNi := inv_natCast_mem_adicCompletionIntegers v N hNv
    have hNF : ((N : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
      rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
      exact (map_ne_zero _).mpr (by exact_mod_cast hN0)
    have h := one_tmul_mul_mem_localBox Λ₁ v hNi (hmNv v)
    rwa [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hNF,
      ← Algebra.TensorProduct.one_def, one_mul] at h

  have hNΛ : ∀ z ∈ Λ₁, ((N : ℕ) : ℤ) • z ∈ Submodule.conjByFiniteIdele Λ₁ m := nsmul_mem_of_relIndex_eq hRN
  have hbox2 : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
      x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ₁ m) v ↔
        ((mv v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) * x * (mv v) ∈ Submodule.localBox Λ₁ v := by
    intro v x
    rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ₁ h1o.fg h1o.spanTop m v x, ← hmvval, ← hmvinv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    · intro hx
      exact ⟨_, hx, by rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]⟩
  have hboxR : ∀ v, Submodule.localBox (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m) v =
      Submodule.localBox Λ₁ v ⊓ Submodule.localBox (Submodule.conjByFiniteIdele Λ₁ m) v := fun v =>
    Submodule.localBox_inf Λ₁ _ h1o.fg h1o.spanTop h2o.fg h2o.spanTop v

  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 ℚ) → ℕ, ∀ v,
      e v = (Submodule.localBox (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m) v).relIndex (Submodule.localBox Λ₁ v) :=
    ⟨_, fun v => rfl⟩
  have hprod : ∏ᶠ v, e v = N := by
    rw [← hRN, Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ₁ _ h1o.fg h1o.spanTop hRo.fg hRo.spanTop
      inf_le_left]
    exact finprod_congr fun v => he v
  have he1 : ∀ v, ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → e v = 1 := by
    intro v hNv
    rw [he, hboxR, inf_eq_left.mpr (localBox_le_of_nsmul_mem hN0 hNΛ v (inv_natCast_mem_adicCompletionIntegers v N hNv))]
    exact AddSubgroup.relIndex_self _
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v, v ∈ S ↔ ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have hne : (Ideal.span {((N : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN0
    refine ⟨(Ideal.finite_factors hne).toFinset, fun v => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have hsupp : Function.mulSupport e ⊆ (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Finset.mem_coe, hS]
    by_contra h
    exact hv (he1 v h)
  have hprodS : ∏ v ∈ S, e v = N := by rw [← finprod_eq_prod_of_mulSupport_subset e hsupp]; exact hprod

  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ n : ℕ, e v = (Rat.HeightOneSpectrum.natGenerator v) ^ n ∧
      ((∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) → n = 0) ∧
      ((¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) →
        ∃ (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)),
          (∀ r : v.adicCompletion ℚ,
            φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
          (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
            z ∈ Submodule.localBox Λ₁ v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ) ∧
          ∃ (s : v.adicCompletion ℚ) (k₁ W : GL (Fin 2) (v.adicCompletion ℚ)),
            s ≠ 0 ∧ IsInt (v.adicCompletionIntegers ℚ) (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
            IsInt (v.adicCompletionIntegers ℚ) ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
            IsInt (v.adicCompletionIntegers ℚ) (W : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
            IsInt (v.adicCompletionIntegers ℚ) ((W⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
            φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
              Matrix.scalar (Fin 2) s * ((k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
                Matrix.diagonal ![(1 : v.adicCompletion ℚ),
                  ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : v.adicCompletion ℚ) ^ n] *
                (W : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))) := by
    intro v
    by_cases hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x
    · refine ⟨0, ?_, fun _ => rfl, fun h => absurd hdiv h⟩
      rw [pow_zero, he, hboxR, ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv hΛ₁ hΛ₂,
        inf_idem]
      exact AddSubgroup.relIndex_self _
    ·
      obtain ⟨φ, hφ, h₁⟩ := exists_standard_frame hab hΛ₁ v hdiv
      obtain ⟨Hm, hHmval, hHminv⟩ : ∃ Hm : GL (Fin 2) (v.adicCompletion ℚ),
          (Hm : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = φ (mv v : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∧
          ((Hm⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
            φ (((mv v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
        ⟨Units.map φ.toRingHom.toMonoidHom (mv v), rfl, Units.coe_map_inv _ _⟩
      obtain ⟨s, t, k₁, k₂, hs0, ht0, htO, hk1, hk1i, hk2, hk2i, hH⟩ :=
        Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring (v.adicCompletionIntegers ℚ) Hm
      obtain ⟨n, u, htu0⟩ := exists_unit_mul_pow (Rat.HeightOneSpectrum.prime_natGenerator v) v (natGenerator_mem v) t htO ht0
      obtain ⟨L, hL⟩ : ∃ L : v.adicCompletion ℚ, ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : v.adicCompletion ℚ) = L := ⟨_, rfl⟩
      obtain ⟨uF, huFdef⟩ : ∃ uF : v.adicCompletion ℚ, ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = uF := ⟨_, rfl⟩
      have htu' : t = uF * L ^ n := by rw [htu0, hL, huFdef]
      have hℓF : L ≠ 0 := by
        rw [← hL, ← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
        exact (map_ne_zero _).mpr (by exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero)
      have hℓn : L ^ n ≠ 0 := pow_ne_zero _ hℓF
      have huFO : uF ∈ v.adicCompletionIntegers ℚ := huFdef ▸ u.1.2
      have h1u : (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * uF = 1 := by
        have h1 := congrArg (fun z : v.adicCompletionIntegers ℚ => (z : v.adicCompletion ℚ)) u.inv_val
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one, huFdef] at h1
        exact h1
      have huF : uF ≠ 0 := right_ne_zero_of_mul_eq_one h1u
      have huFiO : uF⁻¹ ∈ v.adicCompletionIntegers ℚ := by
        have h2 : uF⁻¹ = (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ huF]; exact h1u
        rw [h2]; exact (u⁻¹).1.2
      obtain ⟨Dn, hDn, hDni⟩ := exists_GL (Matrix.diagonal ![(1 : v.adicCompletion ℚ), L ^ n])
        (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (L ^ n)⁻¹]) (diag_mul_diag_inv' (L ^ n) hℓn) (diag_inv_mul_diag' (L ^ n) hℓn)
      obtain ⟨U, hU, hUi⟩ := exists_GL (Matrix.diagonal ![(1 : v.adicCompletion ℚ), uF])
        (Matrix.diagonal ![(1 : v.adicCompletion ℚ), uF⁻¹]) (diag_mul_diag_inv' uF huF) (diag_inv_mul_diag' uF huF)
      obtain ⟨Ssc, hSsc, hSsci⟩ := exists_GL (Matrix.scalar (Fin 2) s) (Matrix.scalar (Fin 2) s⁻¹)
        (scalar_mul_scalar_inv s hs0) (scalar_inv_mul_scalar s hs0)
      obtain ⟨W, hWdef⟩ : ∃ W : GL (Fin 2) (v.adicCompletion ℚ), W = U * k₂ := ⟨_, rfl⟩
      have hUint : IsInt (v.adicCompletionIntegers ℚ) (U : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
        rw [hU]; exact isInt_diagonal _ (one_mem _) huFO
      have hUiint : IsInt (v.adicCompletionIntegers ℚ) ((U⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
        rw [hUi]; exact isInt_diagonal _ (one_mem _) huFiO
      have hWint : IsInt (v.adicCompletionIntegers ℚ) (W : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
        rw [hWdef, Units.val_mul]; exact IsInt.mul _ hUint hk2
      have hWiint : IsInt (v.adicCompletionIntegers ℚ) ((W⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
        rw [hWdef, mul_inv_rev, Units.val_mul]; exact IsInt.mul _ hk2i hUiint

      have hHmGL : Hm = Ssc * k₁ * Dn * W := by
        apply Units.ext
        rw [hH, smul_eq_scalar_mul, Units.val_mul, Units.val_mul, Units.val_mul, hSsc, hDn, hWdef, Units.val_mul, hU,
          htu', mul_comm uF, ← diag_mul_diag]
        exact assoc5 _ _ _ _ _

      have hev : e v = (Rat.HeightOneSpectrum.natGenerator v) ^ n := by
        rw [he]
        refine QuaternionAlgebra.relIndex_eq_pow_of_forall_mem_iff_conj_diagonal_integral hab v
          (Rat.HeightOneSpectrum.prime_natGenerator v) (natGenerator_mem v) φ hφ (Submodule.localBox Λ₁ v) h₁ k₁ hk1 hk1i n
          (Submodule.localBox (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m) v) ?_
        intro z
        rw [hboxR, AddSubgroup.mem_inf, hbox2 v z, h₁, h₁, map_mul, map_mul, ← hHmval, ← hHminv, hHmGL]
        simp only [mul_inv_rev, Units.val_mul, hSsc, hSsci]
        rw [conj_decomp s hs0]
        refine and_congr_right fun _ => ?_
        show IsInt (v.adicCompletionIntegers ℚ) _ ↔ IsInt (v.adicCompletionIntegers ℚ) _
        rw [isInt_conj_iff _ W hWint hWiint, assoc_conj, hDn, hDni, ← hL]
      refine ⟨n, hev, fun h => absurd h hdiv, fun _ => ⟨φ, hφ, h₁, s, k₁, W, hs0, hk1, hk1i, hWint, hWiint, ?_⟩⟩
      rw [← hmvval, ← hHmval, hHmGL, Units.val_mul, Units.val_mul, Units.val_mul, hSsc, hDn, hL]
      exact (assoc4 _ _ _ _).symm
  choose n hn using hloc
  have hnfac : ∀ v ∈ S, n v = N.factorization (Rat.HeightOneSpectrum.natGenerator v) :=
    eq_factorization_of_prod_pow_natGenerator_eq S n N
      (by rw [← hprodS]; exact Finset.prod_congr rfl fun v _ => ((hn v).1).symm)
  intro v ℓ hℓ hv hℓN
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓv : Rat.HeightOneSpectrum.natGenerator v = ℓ := natGenerator_eq hℓ v hv
  have hvS : v ∈ S := by
    rw [hS]
    obtain ⟨c, hc⟩ := hℓN
    rw [hc, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv
  have hnvfac : n v = N.factorization ℓ := by rw [hnfac v hvS, hℓv]
  have hnv : n v = padicValNat ℓ N := by rw [hnvfac, Nat.factorization_def N hℓ]
  have hnpos : 0 < n v := by rw [hnv]; exact one_le_padicValNat_of_dvd hN0 hℓN
  have hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := by
    intro h; have := (hn v).2.1 h; omega
  obtain ⟨φ, hφ, h₁, s, k₁, W, hs0, hk1, hk1i, hW, hWi, hφm⟩ := (hn v).2.2 hndiv
  refine ⟨hndiv, φ, hφ, h₁, ?_⟩
  rw [hℓv] at hφm

  have hℓF : ((ℓ : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by exact_mod_cast hℓ.ne_zero)
  have hℓn : ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (n v) ≠ 0 := pow_ne_zero _ hℓF
  have hNF : ((N : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by exact_mod_cast hN0)
  obtain ⟨Dn, hDn, hDni⟩ := exists_GL
    (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (n v)])
    (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((ℓ : ℕ) : v.adicCompletion ℚ) ^ (n v))⁻¹])
    (diag_mul_diag_inv' (((ℓ : ℕ) : v.adicCompletion ℚ) ^ (n v)) hℓn) (diag_inv_mul_diag' (((ℓ : ℕ) : v.adicCompletion ℚ) ^ (n v)) hℓn)
  obtain ⟨Ssc, hSsc, hSsci⟩ := exists_GL (Matrix.scalar (Fin 2) s) (Matrix.scalar (Fin 2) s⁻¹)
    (scalar_mul_scalar_inv s hs0) (scalar_inv_mul_scalar s hs0)
  obtain ⟨Nsc, hNsc, hNsci⟩ := exists_GL (Matrix.scalar (Fin 2) ((N : ℕ) : v.adicCompletion ℚ))
    (Matrix.scalar (Fin 2) (((N : ℕ) : v.adicCompletion ℚ))⁻¹) (scalar_mul_scalar_inv _ hNF) (scalar_inv_mul_scalar _ hNF)
  obtain ⟨Hm, hHmval, hHminv⟩ : ∃ Hm : GL (Fin 2) (v.adicCompletion ℚ),
      (Hm : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = φ (mv v : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∧
      ((Hm⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
        φ (((mv v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
    ⟨Units.map φ.toRingHom.toMonoidHom (mv v), rfl, Units.coe_map_inv _ _⟩
  have hHmGL : Hm = Ssc * k₁ * Dn * W := by
    apply Units.ext
    rw [hHmval, hmvval, hφm, Units.val_mul, Units.val_mul, Units.val_mul, hSsc, hDn]
    exact assoc4 _ _ _ _
  have hSk : Ssc * k₁ = k₁ * Ssc := comm_of_val_eq_scalar Ssc k₁ s hSsc
  have hSik : Ssc⁻¹ * k₁ = k₁ * Ssc⁻¹ := comm_of_val_eq_scalar Ssc⁻¹ k₁ s⁻¹ hSsci
  have hNc : ∀ g : GL (Fin 2) (v.adicCompletion ℚ), Nsc * g = g * Nsc := fun g => comm_of_val_eq_scalar Nsc g _ hNsc

  have hsO : s ∈ v.adicCompletionIntegers ℚ := by
    have hX : IsInt (v.adicCompletionIntegers ℚ) (((k₁⁻¹ * Hm * W⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) := by
      rw [Units.val_mul, Units.val_mul, hHmval, hmvval]
      exact IsInt.mul _ (IsInt.mul _ hk1i ((h₁ _).mp (hm₁v v))) hWi
    have e1 : k₁⁻¹ * Hm * W⁻¹ = Ssc * Dn := by
      rw [hHmGL, hSk]; group
    rw [e1, Units.val_mul, hSsc, hDn] at hX
    have h00 := hX 0 0
    rwa [entry00_scalar_diag] at h00

  have hsiO : s⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    have hY : IsInt (v.adicCompletionIntegers ℚ) (((W * (Nsc * Hm⁻¹) * k₁ : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hNsc, hHminv, hmvinv, ← smul_one_eq_scalar, ← hφ, ← map_mul]
      exact IsInt.mul _ (IsInt.mul _ hW ((h₁ _).mp (hmNv v))) hk1
    have e2 : W * (Nsc * Hm⁻¹) * k₁ = Nsc * Dn⁻¹ * Ssc⁻¹ := by
      rw [hHmGL]
      calc W * (Nsc * (Ssc * k₁ * Dn * W)⁻¹) * k₁
          = (W * Nsc) * (W⁻¹ * Dn⁻¹ * k₁⁻¹ * Ssc⁻¹) * k₁ := by group
        _ = (Nsc * W) * (W⁻¹ * Dn⁻¹ * k₁⁻¹ * Ssc⁻¹) * k₁ := by rw [hNc W]
        _ = Nsc * Dn⁻¹ * k₁⁻¹ * (Ssc⁻¹ * k₁) := by group
        _ = Nsc * Dn⁻¹ * k₁⁻¹ * (k₁ * Ssc⁻¹) := by rw [hSik]
        _ = Nsc * Dn⁻¹ * Ssc⁻¹ := by group
    rw [e2, Units.val_mul, Units.val_mul, hNsc, hDni, hSsci] at hY
    have h11 := hY 1 1
    rw [entry11_scalar_diag_scalar] at h11

    have hNsplit : ((N : ℕ) : v.adicCompletion ℚ) = ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (n v) *
        ((N / ℓ ^ N.factorization ℓ : ℕ) : v.adicCompletion ℚ) := by
      have h := congrArg (Nat.cast : ℕ → v.adicCompletion ℚ) (Nat.ordProj_mul_ordCompl_eq_self N ℓ).symm
      rw [Nat.cast_mul, Nat.cast_pow] at h
      rw [hnvfac]; exact h
    rw [hNsplit, mul_comm (((ℓ : ℕ) : v.adicCompletion ℚ) ^ n v) _, mul_assoc ((N / ℓ ^ N.factorization ℓ : ℕ) : v.adicCompletion ℚ),
      mul_inv_cancel₀ hℓn, mul_one] at h11

    have hN'v : ((N / ℓ ^ N.factorization ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [← natGenerator_dvd_iff', hℓv]
      exact Nat.not_dvd_ordCompl hℓ hN0
    have hN'i := inv_natCast_mem_adicCompletionIntegers v _ hN'v
    have hN'F : ((N / ℓ ^ N.factorization ℓ : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
      rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
      exact (map_ne_zero _).mpr (by exact_mod_cast (Nat.ordCompl_pos ℓ hN0).ne')
    have := mul_mem hN'i h11
    rwa [← mul_assoc, inv_mul_cancel₀ hN'F, one_mul] at this
  refine ⟨Ssc * k₁, W, ?_, ?_, hW, hWi, ?_⟩
  · rw [Units.val_mul, hSsc]; exact IsInt.mul _ (isInt_scalar _ hsO) hk1
  · rw [mul_inv_rev, Units.val_mul, hSsci]; exact IsInt.mul _ hk1i (isInt_scalar _ hsiO)
  · rw [← hmvval, ← hHmval, hHmGL, Units.val_mul, Units.val_mul, Units.val_mul, hDn, hnv]

end S_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq (solution)
