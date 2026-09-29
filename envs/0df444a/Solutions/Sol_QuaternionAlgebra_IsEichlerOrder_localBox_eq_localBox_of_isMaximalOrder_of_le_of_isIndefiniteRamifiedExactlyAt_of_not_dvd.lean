-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a4732045-9e04-5193-862e-5af0beef0d7f

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace HeckeLocal
variable {a b : ℚ}
def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}
theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl
theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩
end HeckeLocal

namespace C8N
namespace LocalAtQ

variable (K : Type*) [Field K]

def alMat (q : K) : Matrix (Fin 2) (Fin 2) K := !![0, 1; q, 0]

theorem alMat_mul_alMat (q : K) : alMat K q * alMat K q = q • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [alMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem alMat_eq_diagonal_mul_swap (q : K) :
    alMat K q = Matrix.diagonal ![(1 : K), q] * !![(0 : K), 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [alMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_alMat (q : K) : (alMat K q).det = -q := by
  simp [alMat, Matrix.det_fin_two]

theorem alMat_inv (q : K) (hq : q ≠ 0) : (alMat K q)⁻¹ = !![(0 : K), q⁻¹; 1, 0] := by
  have h : alMat K q * !![(0 : K), q⁻¹; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [alMat, Matrix.mul_apply, Fin.sum_univ_two, hq]
  exact Matrix.inv_eq_right_inv h

theorem smul_alMat_inv (q : K) (hq : q ≠ 0) : q • (alMat K q)⁻¹ = alMat K q := by
  rw [alMat_inv K q hq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [alMat, hq]

theorem inv_smul_alMat (q : K) (hq : q ≠ 0) : q⁻¹ • alMat K q = (alMat K q)⁻¹ := by
  rw [alMat_inv K q hq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [alMat, hq]

end C8N.LocalAtQ

namespace C8N
namespace LocalAtQ

open Matrix

variable {a b : ℚ}

section Swap

variable {K : Type*} [Field K]

def swapMat (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem swapMat_conj_apply (Y : Matrix (Fin 2) (Fin 2) K) :
    swapMat K * Y * swapMat K = !![Y 1 1, Y 1 0; Y 0 1, Y 0 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem forall_swapMat_conj_mem_iff {σ : Type*} [SetLike σ K] (S : σ) (Y : Matrix (Fin 2) (Fin 2) K) :
    (∀ i j, (swapMat K * Y * swapMat K) i j ∈ S) ↔ ∀ i j, Y i j ∈ S := by
  rw [swapMat_conj_apply]
  constructor
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using h 1 1
    · simpa using h 1 0
    · simpa using h 0 1
    · simpa using h 0 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using h 1 1
    · simpa using h 1 0
    · simpa using h 0 1
    · simpa using h 0 0

theorem alMat_inv_mul_mul_alMat (q : K) (hq : q ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K) :
    (alMat K q)⁻¹ * Y * alMat K q =
      swapMat K * (Matrix.diagonal ![(1 : K), q⁻¹] * Y * Matrix.diagonal ![(1 : K), q]) * swapMat K := by
  rw [alMat_inv K q hq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [alMat, swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.vecMul, dotProduct, hq, mul_comm]

theorem conj_smul_one (hm hi : Matrix (Fin 2) (Fin 2) K) (hmi : hm * hi = 1) (c : K) :
    hm * (c • (1 : Matrix (Fin 2) (Fin 2) K)) * hi = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hmi]

theorem conj_smul_one_mul (hi hm : Matrix (Fin 2) (Fin 2) K) (c : K) (M : Matrix (Fin 2) (Fin 2) K) :
    hi * (c • (1 : Matrix (Fin 2) (Fin 2) K) * M) * hm = c • (hi * M * hm) := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem mul_conj_mul_conj (hm hi : Matrix (Fin 2) (Fin 2) K) (him : hi * hm = 1) (A : Matrix (Fin 2) (Fin 2) K) :
    hm * A * hi * (hm * A * hi) = hm * (A * A) * hi := by
  rw [show hm * A * hi * (hm * A * hi) = hm * (A * (hi * hm) * A) * hi by simp only [mul_assoc], him, mul_one]

theorem conj_sandwich (hm hi : Matrix (Fin 2) (Fin 2) K) (him : hi * hm = 1) (P Q Y : Matrix (Fin 2) (Fin 2) K) :
    hi * (hm * P * hi * Y * (hm * Q * hi)) * hm = P * (hi * Y * hm) * Q := by
  rw [show hi * (hm * P * hi * Y * (hm * Q * hi)) * hm = (hi * hm) * P * (hi * Y * hm) * Q * (hi * hm) by
    simp only [mul_assoc], him, one_mul, mul_one]

end Swap

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem inv_natCast_notMem_adicCompletionIntegers (q : ℕ) (hq : q.Prime)
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((q : v.adicCompletion ℚ))⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  have hq0 : ((q : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by exact_mod_cast hq.ne_zero)
  have hval : Valued.v ((q : ℕ) : v.adicCompletion ℚ) < 1 := by
    have h1 : ((q : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((q : ℕ) : 𝓞 ℚ) := by
      rw [map_natCast]
    rw [h1]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((q : ℕ) : 𝓞 ℚ)
    erw [h2]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hqv
  intro hmem
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at hmem
  have : (1 : _) < (Valued.v ((q : ℕ) : v.adicCompletion ℚ))⁻¹ :=
    one_lt_inv_iff₀.mpr ⟨(Valuation.pos_iff _).mpr hq0, hval⟩
  exact absurd (lt_of_lt_of_le this hmem) (lt_irrefl 1)

theorem natCast_mem_adicCompletionIntegers (n : ℕ) : ((n : v.adicCompletion ℚ)) ∈ v.adicCompletionIntegers ℚ :=
  natCast_mem _ n

end Local

end C8N.LocalAtQ

namespace C8N
namespace LocalAtQ

open Matrix

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

set_option synthInstance.maxHeartbeats 320000 in

theorem exists_atkinLehner_of_box
    (q : ℕ) (hq : q.Prime) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (O : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ) * (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O ∧
        algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)⁻¹ * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O) ∧
      ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)) ∧
      ∀ O' : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
        (∀ x, x ∈ O' ↔ (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * w ∈ O) →
        (O ⊓ O').relIndex O = q := by

  set hm : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hhm
  set hi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hhi
  have hmi : hm * hi = 1 := by
    rw [hhm, hhi, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have him : hi * hm = 1 := by
    rw [hhm, hhi, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hqK : ((q : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by exact_mod_cast hq.ne_zero)

  set A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := alMat (v.adicCompletion ℚ) (q : v.adicCompletion ℚ) with hA
  have hAdet : A.det ≠ 0 := by rw [hA, det_alMat]; exact neg_ne_zero.mpr hqK
  let AU : GL (Fin 2) (v.adicCompletion ℚ) := Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet
  have hAU : ((AU : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = A := Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hAdet
  let wM : GL (Fin 2) (v.adicCompletion ℚ) := h * AU * h⁻¹
  let w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ := Units.map φ.symm.toRingHom.toMonoidHom wM
  have hwM : ((wM : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = hm * A * hi := by
    show (((h * AU * h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = hm * A * hi
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hAU]
  have hw : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = φ.symm (hm * A * hi) := by
    show ((Units.map φ.symm.toRingHom.toMonoidHom wM : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = _
    rw [Units.coe_map, ← hwM]
    rfl
  have hwMinv : ((wM⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = hm * A⁻¹ * hi := by
    have h1 : ((wM⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = ((h * AU⁻¹ * h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
      congr 1
      show (h * AU * h⁻¹)⁻¹ = h * AU⁻¹ * h⁻¹
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [h1, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.coe_units_inv, hAU]
  have hwi : (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = φ.symm (hm * A⁻¹ * hi) := by
    show (((Units.map φ.symm.toRingHom.toMonoidHom wM)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = _
    rw [← map_inv (Units.map φ.symm.toRingHom.toMonoidHom) wM, Units.coe_map, hwMinv]
    rfl

  have halg : ∀ r : ℚ, φ (algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) r) = algebraMap ℚ (v.adicCompletion ℚ) r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply', hφ]

  have hconj : ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), hi * φ (φ.symm (hm * M * hi)) * hm = M := by
    intro M
    rw [RingEquiv.apply_symm_apply, ← mul_assoc, ← mul_assoc, him, one_mul, mul_assoc, him, mul_one]

  have hAint : ∀ i j, A i j ∈ v.adicCompletionIntegers ℚ := by
    intro i j
    rw [hA]
    fin_cases i <;> fin_cases j
    · simp [alMat, zero_mem]
    · simp [alMat, one_mem]
    · simpa [alMat] using natCast_mem_adicCompletionIntegers v q
    · simp [alMat, zero_mem]
  have hAinv01 : (A⁻¹) 0 1 = ((q : v.adicCompletion ℚ))⁻¹ := by
    rw [hA, alMat_inv _ _ hqK]; simp
  have hqAinv : algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ) • A⁻¹ = A := by
    rw [map_natCast, hA, smul_alMat_inv _ _ hqK]
  have hqinvA : (algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ))⁻¹ • A = A⁻¹ := by
    rw [map_natCast, hA, inv_smul_alMat _ _ hqK]
  refine ⟨w, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    rw [hO, hw]
    intro i j
    rw [hconj A]
    exact hAint i j
  ·
    rw [hO, hwi]
    intro i j
    rw [map_mul, halg, conj_smul_one_mul, hconj, hqAinv]
    exact hAint i j
  ·
    rw [hO, hwi]
    intro hall
    have h01 := hall 0 1
    rw [hconj, hAinv01] at h01
    exact inv_natCast_notMem_adicCompletionIntegers v q hq hqv h01
  ·
    rw [hO, hw]
    intro hall
    have h01 := hall 0 1
    rw [map_mul, halg, map_inv₀, conj_smul_one_mul, hconj, hqinvA, hAinv01] at h01
    exact inv_natCast_notMem_adicCompletionIntegers v q hq hqv h01
  ·
    apply φ.injective
    rw [map_mul, hw, RingEquiv.apply_symm_apply, halg, map_natCast]
    rw [mul_conj_mul_conj hm hi him, hA, alMat_mul_alMat, conj_smul_one hm hi hmi]
  ·
    intro O' hO'
    have hO'' : ∀ x, x ∈ O' ↔ ∀ i j,
        (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((q : v.adicCompletion ℚ) ^ 1)⁻¹] * hi * φ x * hm *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), (q : v.adicCompletion ℚ) ^ 1]) i j ∈ v.adicCompletionIntegers ℚ := by
      intro x
      rw [hO', hO, map_mul, map_mul, hw, hwi, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        conj_sandwich hm hi him, hA, alMat_inv_mul_mul_alMat (hq := hqK), forall_swapMat_conj_mem_iff, pow_one]
      simp only [Matrix.mul_assoc]
    have key := Matrix.relIndex_inf_conj_diagonal_pow_eq (a := a) (b := b) v q hq hqv φ hφ h 1 O O' hO hO''
    rw [key, pow_one]

end C8N.LocalAtQ

namespace C8N
namespace LocalAtQ

open Matrix

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

theorem natCast_notMem_of_prime_mem {P : Ideal (𝓞 ℚ)} (hP : P ≠ ⊤) (q : ℕ) (hqP : ((q : ℕ) : 𝓞 ℚ) ∈ P)
    (n : ℕ) (hn : Nat.Coprime q n) : ((n : ℕ) : 𝓞 ℚ) ∉ P := by
  intro hnP
  apply hP
  rw [Ideal.eq_top_iff_one]
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hn
  have : (1 : 𝓞 ℚ) = (u : 𝓞 ℚ) * (q : 𝓞 ℚ) + (w : 𝓞 ℚ) * (n : 𝓞 ℚ) := by
    have := congrArg (Int.cast : ℤ → 𝓞 ℚ) huw
    push_cast at this
    exact this.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hqP) (P.mul_mem_left _ hnP)

theorem inv_natCast_mem_adicCompletionIntegers (q : ℕ) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (n : ℕ) (hn : Nat.Coprime q n) :
    ((n : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have hnP := natCast_notMem_of_prime_mem v.isPrime.ne_top q hqv n hn
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((n : ℕ) : 𝓞 ℚ) := by rw [map_natCast]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((n : ℕ) : 𝓞 ℚ)
  erw [h2, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).mpr hnP, inv_one]

theorem prime_natCast_ringOfIntegers {p : ℕ} (hp : p.Prime) : _root_.Prime (p : 𝓞 ℚ) := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
  rw [this]
  exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ

noncomputable def placeOfPrime' (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span {(p : 𝓞 ℚ)},
    (Ideal.span_singleton_prime (prime_natCast_ringOfIntegers hp).ne_zero).mpr (prime_natCast_ringOfIntegers hp), by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero⟩

theorem natCast_mem_placeOfPrime' (p : ℕ) (hp : p.Prime) : ((p : ℕ) : 𝓞 ℚ) ∈ (placeOfPrime' p hp).asIdeal :=
  Ideal.subset_span (Set.mem_singleton _)

theorem ne_zero_and_ne_zero_of_isIndefiniteRamifiedExactlyAt {p₁ p₂ : ℕ} [Fact p₁.Prime] [Fact p₂.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b p₁ p₂) : a ≠ 0 ∧ b ≠ 0 := by
  have hdiv := (hB.2 (placeOfPrime' p₁ Fact.out)).mpr (Or.inl (natCast_mem_placeOfPrime' p₁ Fact.out))
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hdiv
  constructor
  · intro ha0
    have h := hdiv 0 1 0 0 (by rw [ha0]; push_cast; ring)
    exact one_ne_zero h.2.1
  · intro hb0
    have h := hdiv 0 0 1 0 (by rw [hb0]; push_cast; ring)
    exact one_ne_zero h.2.2.1

theorem exists_splitting {p₁ p₂ : ℕ} [Fact p₁.Prime] [Fact p₂.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b p₁ p₂)
    (q : ℕ) (hq : q.Prime) (hq₁ : q ≠ p₁) (hq₂ : q ≠ p₂) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  haveI : CharZero (v.adicCompletion ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

  have hp₁v : ((p₁ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
    natCast_notMem_of_prime_mem v.isPrime.ne_top q hqv p₁ ((Nat.coprime_primes hq Fact.out).mpr hq₁)
  have hp₂v : ((p₂ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
    natCast_notMem_of_prime_mem v.isPrime.ne_top q hqv p₂ ((Nat.coprime_primes hq Fact.out).mpr hq₂)

  have hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun hall => by
    rcases (hB.2 v).mp hall with h | h
    · exact hp₁v h
    · exact hp₂v h
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hnd
  push Not at hnd
  obtain ⟨x₀, x₁, x₂, x₃, h0, hx⟩ := hnd
  obtain ⟨ha0, hb0⟩ := ne_zero_and_ne_zero_of_isIndefiniteRamifiedExactlyAt (a := a) (b := b) hB
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast ha0
  have hb : (b : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hb0
  have hx' : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) := fun h => hx h.1 h.2.1 h.2.2.1 h.2.2.2
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero (v.adicCompletion ℚ) two_ne_zero (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ)
    ha hb x₀ x₁ x₂ x₃ hx' h0
  obtain ⟨φ, hφ, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := (a : v.adicCompletion ℚ)) (d₂ := (0 : v.adicCompletion ℚ)) (d₃ := (b : v.adicCompletion ℚ))
    (eq_ratCast _ a) (by simp) (eq_ratCast _ b) ψ
  exact ⟨φ, hφ⟩

end C8N.LocalAtQ

namespace C8N
namespace LocalAtQ

open Matrix

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

theorem nsmul_mem_of_relIndex_eq {R Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (hN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ₁) :
    N • z ∈ R := by
  have hcard : Nat.card (Λ₁.toAddSubgroup ⧸ R.toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup) = N := by
    rw [← AddSubgroup.index_eq_card]; exact hN
  have h0 : N • (QuotientAddGroup.mk (⟨z, hz⟩ : Λ₁.toAddSubgroup) :
      Λ₁.toAddSubgroup ⧸ R.toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup) = 0 := by
    rw [← hcard]; exact card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
  exact h0

theorem localBox_eq_of_relIndex_eq {R Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hle : R ≤ Λ₁) {N : ℕ} (hN0 : N ≠ 0)
    (hN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) (hNv : ((N : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ) :
    Submodule.localBox R v = Submodule.localBox Λ₁ v := by
  refine le_antisymm (HeckeLocal.localBox_mono hle v) ?_
  intro x hx
  rw [HeckeLocal.mem_localBox_iff_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    have hNK : ((N : v.adicCompletion ℚ)) ≠ 0 := by
      rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
      exact (map_ne_zero _).mpr (by exact_mod_cast hN0)

    have key : z ⊗ₜ[ℚ] c = ((N : ℤ) • z) ⊗ₜ[ℚ] (((N : v.adicCompletion ℚ))⁻¹ * c) := by
      rw [TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast, ← mul_assoc, mul_inv_cancel₀ hNK, one_mul]
    rw [key]
    refine AddSubgroup.subset_closure ⟨(N : ℤ) • z, ?_, ((N : v.adicCompletion ℚ))⁻¹ * c, mul_mem hNv hc, rfl⟩
    rw [natCast_zsmul]
    exact nsmul_mem_of_relIndex_eq hN hz
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul m x _ hx => exact zsmul_mem hx m

theorem exists_local_atkinLehner {p₁ p₂ : ℕ} [Fact p₁.Prime] [Fact p₂.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b p₁ p₂)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hq₁ : q ≠ p₁) (hq₂ : q ≠ p₂) (hqN : ¬ q ∣ N) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
        algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ) * (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
        (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
        algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)⁻¹ * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
      ((q : ℚ) • (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
        (q : ℚ)⁻¹ • (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
      ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)) ∧
      ∀ O' : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
        (∀ x, x ∈ O' ↔ (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * w ∈ Submodule.localBox R v) →
        (Submodule.localBox R v ⊓ O').relIndex (Submodule.localBox R v) = q := by

  obtain ⟨φ, hφ⟩ := exists_splitting v hB q hq hq₁ hq₂ hqv

  obtain ⟨Λ₁, hΛ₁, hle, hN⟩ := hR.exists_le_isMaximalOrder
  have hN0 : N ≠ 0 := by rintro rfl; exact hqN (dvd_zero q)
  have hNv : ((N : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ :=
    inv_natCast_mem_adicCompletionIntegers v q hqv N ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN)
  have hbox : Submodule.localBox R v = Submodule.localBox Λ₁ v := localBox_eq_of_relIndex_eq v hle hN0 hN hNv

  obtain ⟨h, hh⟩ := hΛ₁.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers v φ hφ
  have hO : ∀ x, x ∈ Submodule.localBox R v ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by
    intro x; rw [hbox]; exact hh x

  obtain ⟨w, ⟨ha1, ha2, ha3, ha4⟩, hb, hd⟩ := exists_atkinLehner_of_box v q hq hqv φ hφ h (Submodule.localBox R v) hO
  refine ⟨w, ⟨ha1, ha2, ha3, ha4⟩, ⟨?_, ?_⟩, hb, hd⟩
  · have e : (q : ℚ) • (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ) * (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
      exact Algebra.smul_def (q : ℚ) (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
    rw [e]; exact ha2
  · have e : (q : ℚ)⁻¹ • (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)⁻¹ * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
      exact Algebra.smul_def (q : ℚ)⁻¹ (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
    rw [e]; exact ha4

end C8N.LocalAtQ

namespace C8N
namespace LocalAtQ

open Matrix

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

section ScaledConj
variable {K : Type*} [Field K]
theorem scaled_conj_eq (e : K) (he0 : e ≠ 0) (gm gi Y : Matrix (Fin 2) (Fin 2) K) :
    (e • gi) * Y * (e⁻¹ • gm) = gi * Y * gm := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ he0, one_smul]
theorem scaled_conj_eq' (e : K) (he0 : e ≠ 0) (gm gi Y : Matrix (Fin 2) (Fin 2) K) :
    (e⁻¹ • gm) * Y * (e • gi) = gm * Y * gi := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ he0, one_smul]
end ScaledConj

section LocalMax

theorem mul_apply_mem_of_forall_mem {σ : Type*} [SetLike σ (v.adicCompletion ℚ)] [SubringClass σ (v.adicCompletion ℚ)] (O : σ)
    (A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (i j : Fin 2) : (A * B) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

theorem inv_mul_single_mul_apply (g gi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (k i₀ i j₀ : Fin 2) :
    (gi * Matrix.single k i₀ (1 : v.adicCompletion ℚ) * g) i j₀ = gi i k * g i₀ j₀ := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases k <;> fin_cases i₀ <;> simp [Matrix.single]

theorem forall_conj_mem_of_forall_inv_conj_mem (g : GL (Fin 2) (v.adicCompletion ℚ))
    (hg : ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, (((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y * (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ) :
    ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y * ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by
  set gm : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hgm
  set gi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hgi
  have hmi : gm * gi = 1 := by
    rw [hgm, hgi, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have him : gi * gm = 1 := by
    rw [hgm, hgi, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]

  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun p => Valued.v (gm p.1 p.2)) ⟨(0, 0), Finset.mem_univ _⟩
  set e : v.adicCompletion ℚ := gm p.1 p.2 with he
  have he0 : e ≠ 0 := by
    intro he0
    have hall : ∀ i j, gm i j = 0 := by
      intro i j
      have hle := hp (i, j) (Finset.mem_univ _)
      rw [he0, map_zero, le_zero_iff, map_eq_zero] at hle
      exact hle
    have hg0 : gm = 0 := by ext i j : 1; exact hall i j
    have : (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 0 := by rw [← hmi, hg0, zero_mul]
    exact one_ne_zero this

  set g₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := e⁻¹ • gm with hg₀
  set g₀i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := e • gi with hg₀i
  have hg₀int : ∀ i j, g₀ i j ∈ v.adicCompletionIntegers ℚ := by
    intro i j
    rw [hg₀, Matrix.smul_apply, smul_eq_mul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀,
      inv_mul_le_iff₀ ((Valuation.pos_iff _).mpr he0), mul_one]
    exact hp (i, j) (Finset.mem_univ _)
  have hg₀p : g₀ p.1 p.2 = 1 := by
    rw [hg₀, Matrix.smul_apply, smul_eq_mul, ← he, inv_mul_cancel₀ he0]
  have hconj : ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), g₀i * Y * g₀ = gi * Y * gm := fun Y =>
    scaled_conj_eq e he0 gm gi Y

  have hg₀iint : ∀ i k, g₀i i k ∈ v.adicCompletionIntegers ℚ := by
    intro i k
    have hY : ∀ i' j', (Matrix.single k p.1 (1 : v.adicCompletion ℚ)) i' j' ∈ v.adicCompletionIntegers ℚ := by
      intro i' j'
      by_cases h : k = i' ∧ p.1 = j'
      · obtain ⟨rfl, rfl⟩ := h
        rw [Matrix.single_apply_same]; exact one_mem _
      · rw [Matrix.single_apply_of_ne (h := h)]; exact zero_mem _
    have h1 := hg (Matrix.single k p.1 (1 : v.adicCompletion ℚ)) hY i p.2
    rw [← hconj, inv_mul_single_mul_apply, hg₀p, mul_one] at h1
    exact h1

  intro Y hY i j
  have hconj' : gm * Y * gi = g₀ * Y * g₀i := (scaled_conj_eq' e he0 gm gi Y).symm
  rw [hconj']
  exact mul_apply_mem_of_forall_mem v (v.adicCompletionIntegers ℚ) _ _
    (mul_apply_mem_of_forall_mem v (v.adicCompletionIntegers ℚ) _ _ hg₀int hY) hg₀iint i j

end LocalMax

end C8N.LocalAtQ

namespace C8N
namespace LocalAtQ

open Matrix

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

theorem localBox_eq_of_isMaximalOrder_of_le {p₁ p₂ : ℕ} [Fact p₁.Prime] [Fact p₂.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b p₁ p₂)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hq₁ : q ≠ p₁) (hq₂ : q ≠ p₂) (hqN : ¬ q ∣ N) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂) (hle₂ : R ≤ Λ₂) :
    Submodule.localBox Λ₂ v = Submodule.localBox R v := by
  obtain ⟨φ, hφ⟩ := exists_splitting v hB q hq hq₁ hq₂ hqv
  obtain ⟨Λ₁, hΛ₁, hle, hN⟩ := hR.exists_le_isMaximalOrder
  have hN0 : N ≠ 0 := by rintro rfl; exact hqN (dvd_zero q)
  have hNv : ((N : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ :=
    inv_natCast_mem_adicCompletionIntegers v q hqv N ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN)
  have hbox : Submodule.localBox R v = Submodule.localBox Λ₁ v := localBox_eq_of_relIndex_eq v hle hN0 hN hNv
  obtain ⟨h₁, hh₁⟩ := hΛ₁.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers v φ hφ
  obtain ⟨h₂, hh₂⟩ := hΛ₂.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers v φ hφ
  have hsub : Submodule.localBox R v ≤ Submodule.localBox Λ₂ v := HeckeLocal.localBox_mono hle₂ v
  refine le_antisymm ?_ hsub

  set hm₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (h₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with e1
  set hi₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := ((h₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with e2
  set hm₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (h₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with e3
  set hi₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := ((h₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with e4
  have hmi₁ : hm₁ * hi₁ = 1 := by
    rw [e1, e2, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have him₁ : hi₁ * hm₁ = 1 := by
    rw [e1, e2, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hmi₂ : hm₂ * hi₂ = 1 := by
    rw [e3, e4, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have him₂ : hi₂ * hm₂ = 1 := by
    rw [e3, e4, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  let g : GL (Fin 2) (v.adicCompletion ℚ) := h₁⁻¹ * h₂
  have hg : ((g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = hi₁ * hm₂ := by
    show (((h₁⁻¹ * h₂ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = _; rw [Matrix.GeneralLinearGroup.coe_mul]
  have hgi : ((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = hi₂ * hm₁ := by
    show ((((h₁⁻¹ * h₂)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = _
    rw [_root_.mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.coe_mul]

  have hcore : ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, (((g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y * (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by
    intro Y hY

    have hx : φ.symm (hm₁ * Y * hi₁) ∈ Submodule.localBox Λ₂ v := by
      apply hsub
      rw [hbox, hh₁, RingEquiv.apply_symm_apply]
      intro i j
      rw [show hi₁ * (hm₁ * Y * hi₁) * hm₁ = (hi₁ * hm₁) * Y * (hi₁ * hm₁) by simp only [mul_assoc], him₁, one_mul, mul_one]
      exact hY i j
    rw [hh₂, RingEquiv.apply_symm_apply] at hx
    intro i j
    rw [hgi, hg, show hi₂ * hm₁ * Y * (hi₁ * hm₂) = hi₂ * (hm₁ * Y * hi₁) * hm₂ by simp only [mul_assoc]]
    exact hx i j
  have hconv := forall_conj_mem_of_forall_inv_conj_mem v g hcore

  intro x hx
  rw [hbox, hh₁]
  rw [hh₂] at hx
  intro i j
  have h1 := hconv (hi₂ * φ x * hm₂) hx i j
  rw [hg, hgi, show hi₁ * hm₂ * (hi₂ * φ x * hm₂) * (hi₂ * hm₁) = hi₁ * (hm₂ * hi₂) * φ x * (hm₂ * hi₂) * hm₁ by
    simp only [mul_assoc], hmi₂, mul_one, mul_one] at h1
  exact h1

end C8N.LocalAtQ

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂) (hle₂ : R ≤ Λ₂) :
    Submodule.localBox Λ₂ v = Submodule.localBox R v :=
  C8N.LocalAtQ.localBox_eq_of_isMaximalOrder_of_le v hB hR ℓ hℓ hℓq hℓq' hℓN hℓv hΛ₂ hle₂

end S_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd (solution)
