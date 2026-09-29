-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/04826bdd-bf52-5383-9bb9-7d687864b16b

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
import Theorems.Thm_QuaternionAlgebra_exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_or_localBox_eq_of_inf_le_of_localBox_iff_conj_diagonal
import Theorems.Thm_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra

namespace Nat
p2m_export "Nat" "prime_iff log count divisors Prime Prime.factorization_self prime_iff_prime_int eq_zero_or_pos card_fin cast_zero card_congr all zero"
p2m_open "Nat"

noncomputable def placesOf (ℓ : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  if h : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) = ⊥ then ∅ else (Ideal.finite_factors h).toFinset

theorem span_natCast_ne_bot {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ

theorem mem_placesOf_iff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOf ℓ ↔ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [placesOf, dif_neg (span_natCast_ne_bot hℓ), Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Ideal.dvd_span_singleton]

theorem inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ placesOf ℓ) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_placesOf_iff hℓ] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  exact hprime.isMaximal (span_natCast_ne_bot hp.ne_zero)

theorem HeightOneSpectrum.eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

end Nat

namespace HeckeLocal

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  have : Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (ℓ : ℕ) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, h4⟩ := hh
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exfalso; apply h4
    rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  rw [Submodule.mem_localBoxUnits_iff]
  refine ⟨finiteAdeleEvalAt_mem_localBox v h1, ?_⟩
  set f := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hf
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) :=
    Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

end HeckeLocal

namespace F3LOC

open Matrix

variable {K : Type*} [Field K] {𝒪 : ValuationSubring K}

local notation "val" => ValuationSubring.valuation 𝒪

theorem mem_iff_val {x : K} : x ∈ 𝒪 ↔ val x ≤ 1 := (𝒪.valuation_le_one_iff x).symm

def IsU (𝒪 : ValuationSubring K) (x : K) : Prop := 𝒪.valuation x = 1

theorem IsU.mem {x : K} (h : IsU 𝒪 x) : x ∈ 𝒪 := mem_iff_val.mpr h.le
theorem IsU.ne_zero {x : K} (h : IsU 𝒪 x) : x ≠ 0 := by rintro rfl; simp [IsU] at h
theorem IsU.inv {x : K} (h : IsU 𝒪 x) : IsU 𝒪 x⁻¹ := by unfold IsU at *; rw [map_inv₀, h, inv_one]
theorem IsU.mul {x y : K} (hx : IsU 𝒪 x) (hy : IsU 𝒪 y) : IsU 𝒪 (x * y) := by unfold IsU at *; rw [map_mul, hx, hy, one_mul]
theorem isU_one : IsU 𝒪 (1 : K) := by unfold IsU; exact map_one _
theorem isU_of_mem_of_inv_mem {x : K} (hx : x ∈ 𝒪) (hxi : x⁻¹ ∈ 𝒪) (hx0 : x ≠ 0) : IsU 𝒪 x := by
  rw [mem_iff_val] at hx hxi
  rw [map_inv₀] at hxi
  refine le_antisymm hx ?_
  have h0 : 0 < val x := zero_lt_iff.mpr ((map_ne_zero _).mpr hx0)
  exact (inv_le_one₀ h0).mp hxi

theorem val_lt_one_of_not_isU {x : K} (hx : x ∈ 𝒪) (hu : ¬ IsU 𝒪 x) : val x < 1 :=
  lt_of_le_of_ne (mem_iff_val.mp hx) hu

theorem isU_or_isU_of_isU_add {a₀ a₁ b₀ b₁ : K} (ha₀ : a₀ ∈ 𝒪) (ha₁ : a₁ ∈ 𝒪) (hb₀ : b₀ ∈ 𝒪) (hb₁ : b₁ ∈ 𝒪)
    (h : IsU 𝒪 (a₀ * b₀ + a₁ * b₁)) : IsU 𝒪 b₀ ∨ IsU 𝒪 b₁ := by
  by_contra hcon
  push_neg at hcon
  have h0 : val (a₀ * b₀) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (mem_iff_val.mp ha₀)) (val_lt_one_of_not_isU hb₀ hcon.1)
  have h1 : val (a₁ * b₁) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (mem_iff_val.mp ha₁)) (val_lt_one_of_not_isU hb₁ hcon.2)
  have := Valuation.map_add_lt (val) h0 h1
  rw [h] at this
  exact lt_irrefl _ this

def IsInt (𝒪 : ValuationSubring K) (y : Matrix (Fin 2) (Fin 2) K) : Prop := ∀ i j, y i j ∈ 𝒪

def IsIntU (𝒪 : ValuationSubring K) (y : Matrix (Fin 2) (Fin 2) K) : Prop :=
  IsInt 𝒪 y ∧ IsUnit y.det ∧ IsInt 𝒪 y⁻¹

theorem IsInt.mul {y z : Matrix (Fin 2) (Fin 2) K} (hy : IsInt 𝒪 y) (hz : IsInt 𝒪 z) : IsInt 𝒪 (y * z) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hy i 0) (hz 0 j)) (mul_mem (hy i 1) (hz 1 j))

theorem IsInt.one : IsInt 𝒪 (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro i j; rw [Matrix.one_apply]; split_ifs <;> simp [one_mem, zero_mem]

theorem IsInt.smul {y : Matrix (Fin 2) (Fin 2) K} (hy : IsInt 𝒪 y) {c : K} (hc : c ∈ 𝒪) : IsInt 𝒪 (c • y) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hy i j)

theorem IsIntU.isInt_conj_iff {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt 𝒪 (k⁻¹ * Y * k) ↔ IsInt 𝒪 Y := by
  have hdet : IsUnit k.det := hk.2.1
  constructor
  · intro h
    have := (hk.1.mul h).mul hk.2.2
    rwa [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      mul_one] at this
  · intro h; exact (hk.2.2.mul h).mul hk.1

theorem IsIntU.exists_isU_col {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (j : Fin 2) :
    IsU 𝒪 (k 0 j) ∨ IsU 𝒪 (k 1 j) := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul k hk.2.1) j) j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  exact isU_or_isU_of_isU_add (hk.2.2 j 0) (hk.2.2 j 1) (hk.1 0 j) (hk.1 1 j) (by rw [h]; exact isU_one)

theorem IsIntU.exists_isU_inv_row {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (i : Fin 2) :
    IsU 𝒪 (k⁻¹ i 0) ∨ IsU 𝒪 (k⁻¹ i 1) := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul k hk.2.1) i) i
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h

  have h' : k 0 i * k⁻¹ i 0 + k 1 i * k⁻¹ i 1 = 1 := by rw [mul_comm (k 0 i), mul_comm (k 1 i)]; exact h
  exact isU_or_isU_of_isU_add (hk.1 0 i) (hk.1 1 i) (hk.2.2 i 0) (hk.2.2 i 1) (by rw [h']; exact isU_one)

theorem IsIntU.smul {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) {u : K} (hu : IsU 𝒪 u) : IsIntU 𝒪 (u • k) := by
  refine ⟨hk.1.smul hu.mem, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin]; exact (hu.ne_zero.isUnit.pow 2).mul hk.2.1
  · have e : (u • k)⁻¹ = u⁻¹ • k⁻¹ := by
      have h1 : u • k = (Units.mk0 u hu.ne_zero) • k := rfl
      rw [h1, Matrix.inv_smul' k (Units.mk0 u hu.ne_zero) hk.2.1, Units.smul_def]
      simp
    rw [e]
    exact hk.2.2.smul hu.inv.mem

theorem IsInt.det_mem {y : Matrix (Fin 2) (Fin 2) K} (hy : IsInt 𝒪 y) : y.det ∈ 𝒪 := by
  rw [Matrix.det_fin_two]; exact sub_mem (mul_mem (hy 0 0) (hy 1 1)) (mul_mem (hy 0 1) (hy 1 0))

theorem IsIntU.isU_det {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) : IsU 𝒪 k.det := by
  refine isU_of_mem_of_inv_mem hk.1.det_mem ?_ hk.2.1.ne_zero
  have h := hk.2.2.det_mem
  rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h

theorem inv_fin_two (k : Matrix (Fin 2) (Fin 2) K) (hk : IsUnit k.det) :
    k⁻¹ = k.det⁻¹ • !![k 1 1, -k 0 1; -k 1 0, k 0 0] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']

section pi

variable (ϖ : K)

def Dm : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![(1 : K), ϖ]

def Dm' : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![ϖ, (1 : K)]

variable {ϖ}

theorem Dm_inv (hϖ0 : ϖ ≠ 0) : (Dm ϖ)⁻¹ = Matrix.diagonal ![(1 : K), ϖ⁻¹] :=
  Matrix.inv_eq_right_inv (by rw [Dm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [hϖ0])

theorem Dm'_inv (hϖ0 : ϖ ≠ 0) : (Dm' ϖ)⁻¹ = Matrix.diagonal ![ϖ⁻¹, (1 : K)] :=
  Matrix.inv_eq_right_inv (by rw [Dm', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [hϖ0])

theorem det_Dm (hϖ0 : ϖ ≠ 0) : (Dm ϖ).det = ϖ := by simp [Dm, Matrix.det_diagonal]
theorem det_Dm' (hϖ0 : ϖ ≠ 0) : (Dm' ϖ).det = ϖ := by simp [Dm', Matrix.det_diagonal]

theorem smul_Dm_inv (hϖ0 : ϖ ≠ 0) : ϖ • (Dm ϖ)⁻¹ = Dm' ϖ := by
  rw [Dm_inv hϖ0, Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hϖ0]

theorem Dm_inv_conj (hϖ0 : ϖ ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K) :
    (Dm ϖ)⁻¹ * Y * Dm ϖ = !![Y 0 0, ϖ * Y 0 1; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  rw [Dm_inv hϖ0, Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem Dm'_inv_conj (hϖ0 : ϖ ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K) :
    (Dm' ϖ)⁻¹ * Y * Dm' ϖ = !![Y 0 0, ϖ⁻¹ * Y 0 1; ϖ * Y 1 0, Y 1 1] := by
  rw [Dm'_inv hϖ0, Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem Dm_inv_mul_mul_Dm' (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) :
    (Dm ϖ)⁻¹ * k * Dm' ϖ = !![ϖ * k 0 0, k 0 1; k 1 0, ϖ⁻¹ * k 1 1] := by
  rw [Dm_inv hϖ0, Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem Dm'_inv_mul_mul_Dm (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) :
    (Dm' ϖ)⁻¹ * k * Dm ϖ = !![ϖ⁻¹ * k 0 0, k 0 1; k 1 0, ϖ * k 1 1] := by
  rw [Dm'_inv hϖ0, Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem mul_Dm' (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) : k * Dm' ϖ = !![ϖ * k 0 0, k 0 1; ϖ * k 1 0, k 1 1] := by
  rw [Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]

theorem mul_Dm_inv (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) : k * (Dm ϖ)⁻¹ = !![k 0 0, ϖ⁻¹ * k 0 1; k 1 0, ϖ⁻¹ * k 1 1] := by
  rw [Dm_inv hϖ0]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]

theorem Dm_mul (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) : Dm ϖ * k = !![k 0 0, k 0 1; ϖ * k 1 0, ϖ * k 1 1] := by
  rw [Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

def IsIw (𝒪 : ValuationSubring K) (ϖ : K) (y : Matrix (Fin 2) (Fin 2) K) : Prop := IsInt 𝒪 y ∧ ϖ⁻¹ * y 1 0 ∈ 𝒪

theorem isIw_iff_isInt_and (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {y : Matrix (Fin 2) (Fin 2) K} : IsIw 𝒪 ϖ y ↔ IsInt 𝒪 y ∧ IsInt 𝒪 ((Dm ϖ)⁻¹ * y * Dm ϖ) := by
  rw [IsIw, Dm_inv_conj hϖ0]
  refine and_congr_right fun hy => ⟨fun h i j => ?_, fun h => by simpa using h 1 0⟩
  fin_cases i <;> fin_cases j
  · simpa using hy 0 0
  · simpa using mul_mem hϖ (hy 0 1)
  · simpa using h
  · simpa using hy 1 1

theorem normalForm (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪) (y : Matrix (Fin 2) (Fin 2) K) (hy : IsUnit y.det)
    (h1 : IsIw 𝒪 ϖ y) (h2 : IsIw 𝒪 ϖ (ϖ • y⁻¹))
    (hii : ∀ Y : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 ((Dm ϖ)⁻¹ * (y⁻¹ * Y * y) * Dm ϖ) ↔ IsInt 𝒪 Y)
    (hiii : ¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 (y⁻¹ * Y * y) ↔ IsInt 𝒪 ((Dm ϖ)⁻¹ * Y * Dm ϖ)) :
    ∃ k : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k ∧ IsU 𝒪 (k 1 1) ∧ y = k * Dm' ϖ := by

  have hDdet : IsUnit (Dm ϖ).det := by rw [det_Dm hϖ0]; exact hϖ0.isUnit
  set g : Matrix (Fin 2) (Fin 2) K := y * Dm ϖ with hg
  have hgdet : IsUnit g.det := by rw [hg, Matrix.det_mul]; exact hy.mul hDdet
  have hginv : g⁻¹ = (Dm ϖ)⁻¹ * y⁻¹ := by rw [hg, Matrix.mul_inv_rev]
  have hgconj : ∀ M : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 M → IsInt 𝒪 (g⁻¹ * M * g) := by
    intro M hM
    have := (hii M).mpr hM
    rwa [hginv, hg, ← mul_assoc, ← mul_assoc, mul_assoc ((Dm ϖ)⁻¹ * y⁻¹)] at *

  have hginvdet : (g⁻¹).det ≠ 0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hgdet.ne_zero
  let G : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (g⁻¹) hginvdet
  have hGcoe : ((G : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = g⁻¹ := rfl
  have hGinv : ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = g := by
    rw [Matrix.coe_units_inv, hGcoe, Matrix.nonsing_inv_nonsing_inv _ hgdet]
  obtain ⟨c, hc1, hc2⟩ :=
    Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem 𝒪 G
      (fun M hM i j => by rw [hGcoe, hGinv]; exact hgconj M hM i j)
  simp only [hGcoe, hGinv] at hc1 hc2

  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hk₀ : IsIntU 𝒪 ((c : K) • g) := by
    refine ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 i j, ?_, ?_⟩
    · rw [Matrix.det_smul, Fintype.card_fin]; exact (hc0.isUnit.pow 2).mul hgdet
    · have e : ((c : K) • g)⁻¹ = (c : K)⁻¹ • g⁻¹ := by
        rw [show (c : K) • g = c • g from rfl, Matrix.inv_smul' g c hgdet, Units.smul_def, Units.val_inv_eq_inv_val]
      rw [e]; intro i j; rw [Matrix.smul_apply, smul_eq_mul, ← Units.val_inv_eq_inv_val]; exact hc1 i j

  have hyeq : y = (c : K)⁻¹ • (((c : K) • g) * (Dm ϖ)⁻¹) := by
    rw [Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc0, one_smul, hg, mul_assoc, Matrix.mul_nonsing_inv _ hDdet, mul_one]
  set k₀ := (c : K) • g with hk₀def

  have ha : (c : K)⁻¹ * ϖ⁻¹ ∈ 𝒪 := by
    have hcol : ∀ i, y i 1 = (c : K)⁻¹ * ϖ⁻¹ * k₀ i 1 := by
      intro i; rw [hyeq, Matrix.smul_apply, smul_eq_mul, mul_Dm_inv hϖ0]
      fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]
    rcases hk₀.exists_isU_col 1 with hu | hu
    · have := mul_mem (h1.1 0 1) hu.inv.mem
      rwa [hcol 0, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this
    · have := mul_mem (h1.1 1 1) hu.inv.mem
      rwa [hcol 1, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this

  have hyinv : y⁻¹ = (c : K) • (Dm ϖ * k₀⁻¹) := by
    rw [hyeq, show ((c : K)⁻¹ • (k₀ * (Dm ϖ)⁻¹)) = (c⁻¹ : Kˣ) • (k₀ * (Dm ϖ)⁻¹) from by rw [Units.smul_def, Units.val_inv_eq_inv_val],
      Matrix.inv_smul' _ c⁻¹ (by rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact hk₀.2.1.mul hDdet.ne_zero.isUnit.inv),
      inv_inv, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hDdet, Units.smul_def]
  have hb : ϖ * (c : K) ∈ 𝒪 := by
    have hrow : ∀ j, (ϖ • y⁻¹) 0 j = ϖ * (c : K) * k₀⁻¹ 0 j := by
      intro j; rw [hyinv, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Dm_mul hϖ0]
      fin_cases j <;> simp [mul_assoc]
    rcases hk₀.exists_isU_inv_row 0 with hu | hu
    · have := mul_mem (h2.1 0 0) hu.inv.mem
      rwa [hrow 0, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this
    · have := mul_mem (h2.1 0 1) hu.inv.mem
      rwa [hrow 1, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this

  have hu : IsU 𝒪 (ϖ * (c : K)) :=
    isU_of_mem_of_inv_mem hb (by rwa [_root_.mul_inv_rev]) (mul_ne_zero hϖ0 hc0)
  refine ⟨(ϖ * (c : K))⁻¹ • k₀, hk₀.smul hu.inv, ?_, ?_⟩
  rotate_left
  ·
    rw [Matrix.smul_mul, hyeq, ← smul_Dm_inv hϖ0, Matrix.mul_smul, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]
  ·
    by_contra hnu
    apply hiii
    set k := (ϖ * (c : K))⁻¹ • k₀ with hkdef
    have hk : IsIntU 𝒪 k := hk₀.smul hu.inv
    have hyk : y = k * Dm' ϖ := by
      rw [hkdef, Matrix.smul_mul, hyeq, ← smul_Dm_inv hϖ0, Matrix.mul_smul, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]

    have hdiv : ϖ⁻¹ * k 1 1 ∈ 𝒪 := hmax _ (hk.1 1 1) hnu
    have hkdet : IsU 𝒪 k.det := hk.isU_det
    set Z := (Dm ϖ)⁻¹ * k * Dm' ϖ with hZ
    have hZdet : IsUnit Z.det := by
      rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, det_Dm hϖ0, det_Dm' hϖ0, Ring.inverse_eq_inv']
      exact (hϖ0.isUnit.inv.mul hk.2.1).mul hϖ0.isUnit
    have hZint : IsInt 𝒪 Z := by
      rw [hZ, Dm_inv_mul_mul_Dm' hϖ0]
      intro i j; fin_cases i <;> fin_cases j
      · simpa using mul_mem hϖ (hk.1 0 0)
      · simpa using hk.1 0 1
      · simpa using hk.1 1 0
      · simpa using hdiv
    have hZinv : Z⁻¹ = (Dm' ϖ)⁻¹ * k⁻¹ * Dm ϖ := by
      rw [hZ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hDdet, mul_assoc]
    have hZinvint : IsInt 𝒪 Z⁻¹ := by
      rw [hZinv, Dm'_inv_mul_mul_Dm hϖ0, inv_fin_two k hk.2.1]
      intro i j; fin_cases i <;> fin_cases j
      · simpa [mul_comm, mul_left_comm, mul_assoc] using mul_mem hdiv hkdet.inv.mem
      · simpa using mul_mem hkdet.inv.mem (neg_mem (hk.1 0 1))
      · simpa using mul_mem hkdet.inv.mem (neg_mem (hk.1 1 0))
      · simpa [mul_comm, mul_left_comm] using mul_mem hϖ (mul_mem hkdet.inv.mem (hk.1 0 0))
    have hZU : IsIntU 𝒪 Z := ⟨hZint, hZdet, hZinvint⟩

    have hyZ : y = Dm ϖ * Z := by rw [hZ, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hDdet, one_mul, hyk]
    intro Y
    rw [hyZ, Matrix.mul_inv_rev, show Z⁻¹ * (Dm ϖ)⁻¹ * Y * (Dm ϖ * Z) = Z⁻¹ * ((Dm ϖ)⁻¹ * Y * Dm ϖ) * Z by
      simp only [mul_assoc]]
    exact hZU.isInt_conj_iff _

def IsB (𝒪 : ValuationSubring K) (ϖ : K) (z : Matrix (Fin 2) (Fin 2) K) : Prop := IsIw 𝒪 ϖ z ∧ IsUnit z.det ∧ IsIw 𝒪 ϖ z⁻¹

def yRep (ϖ t : K) : Matrix (Fin 2) (Fin 2) K := !![ϖ, t; 0, 1]

theorem det_yRep (hϖ0 : ϖ ≠ 0) (t : K) : (yRep ϖ t).det = ϖ := by simp [yRep, Matrix.det_fin_two]

theorem yRep_inv (hϖ0 : ϖ ≠ 0) (t : K) : (yRep ϖ t)⁻¹ = !![ϖ⁻¹, -(ϖ⁻¹ * t); 0, 1] := by
  rw [inv_fin_two _ (by rw [det_yRep hϖ0]; exact hϖ0.isUnit), det_yRep hϖ0]
  ext i j; fin_cases i <;> fin_cases j <;> simp [yRep, hϖ0]

theorem yRep_eq (hϖ0 : ϖ ≠ 0) (t : K) : yRep ϖ t = !![1, t; 0, 1] * Dm' ϖ := by
  rw [mul_Dm' hϖ0]; ext i j; fin_cases i <;> fin_cases j <;> simp [yRep]

theorem isIw_yRep (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {t : K} (ht : t ∈ 𝒪) : IsIw 𝒪 ϖ (yRep ϖ t) := by
  refine ⟨fun i j => ?_, by simp [yRep]⟩
  fin_cases i <;> fin_cases j <;> simp [yRep, hϖ, ht, one_mem, zero_mem]

theorem isIw_smul_yRep_inv (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {t : K} (ht : t ∈ 𝒪) : IsIw 𝒪 ϖ (ϖ • (yRep ϖ t)⁻¹) := by
  rw [yRep_inv hϖ0]
  refine ⟨fun i j => ?_, by simp⟩
  fin_cases i <;> fin_cases j <;> simp [hϖ0, hϖ, ht, neg_mem, one_mem, zero_mem]

theorem not_isIw_yRep_inv (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) (t : K) : ¬ IsIw 𝒪 ϖ (yRep ϖ t)⁻¹ := by
  rw [yRep_inv hϖ0]; intro h
  have := h.1 0 0; simp at this
  exact hϖu (isU_of_mem_of_inv_mem hϖ this hϖ0)

theorem not_isIw_smul_yRep (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) (t : K) : ¬ IsIw 𝒪 ϖ (ϖ⁻¹ • yRep ϖ t) := by
  intro h
  have := h.1 1 1; simp [yRep] at this
  exact hϖu (isU_of_mem_of_inv_mem hϖ this hϖ0)

theorem isInt_conj_yRep_Dm_iff (hϖ0 : ϖ ≠ 0) {t : K} (ht : t ∈ 𝒪) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt 𝒪 ((Dm ϖ)⁻¹ * ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) * Dm ϖ) ↔ IsInt 𝒪 Y := by

  have hU : IsIntU 𝒪 !![(1 : K), t; 0, 1] := by
    refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two], ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [ht, one_mem, zero_mem]
    · rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]
      intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, ht, neg_mem, one_mem, zero_mem]
  have hyD : yRep ϖ t * Dm ϖ = ϖ • !![(1 : K), t; 0, 1] := by
    rw [yRep, Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]
  have e : (Dm ϖ)⁻¹ * ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) * Dm ϖ = (!![(1 : K), t; 0, 1])⁻¹ * Y * !![(1 : K), t; 0, 1] := by
    have h1 : (Dm ϖ)⁻¹ * (yRep ϖ t)⁻¹ = (yRep ϖ t * Dm ϖ)⁻¹ := by rw [Matrix.mul_inv_rev]
    calc (Dm ϖ)⁻¹ * ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) * Dm ϖ
        = ((Dm ϖ)⁻¹ * (yRep ϖ t)⁻¹) * Y * (yRep ϖ t * Dm ϖ) := by simp only [mul_assoc]
      _ = (ϖ • !![(1 : K), t; 0, 1])⁻¹ * Y * (ϖ • !![(1 : K), t; 0, 1]) := by rw [h1, hyD]
      _ = (!![(1 : K), t; 0, 1])⁻¹ * Y * !![(1 : K), t; 0, 1] := by
          rw [show ϖ • !![(1 : K), t; 0, 1] = (Units.mk0 ϖ hϖ0) • !![(1 : K), t; 0, 1] from rfl,
            Matrix.inv_smul' _ (Units.mk0 ϖ hϖ0) hU.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel, one_smul]
  rw [e]; exact hU.isInt_conj_iff Y

theorem not_forall_isInt_conj_yRep_iff (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) (t : K) :
    ¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) ↔ IsInt 𝒪 ((Dm ϖ)⁻¹ * Y * Dm ϖ) := by
  intro h
  have h1 := (h !![(0 : K), 1; 0, 0]).mpr (by
    rw [Dm_inv_conj hϖ0]; intro i j; fin_cases i <;> fin_cases j <;> simp [hϖ, one_mem, zero_mem])
  have := h1 0 1
  rw [yRep_inv hϖ0, yRep] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this
  exact hϖu (isU_of_mem_of_inv_mem hϖ this hϖ0)

theorem isB_conj_unipotent_iff (hϖ0 : ϖ ≠ 0) {s : K} (hs : s ∈ 𝒪) :
    IsB 𝒪 ϖ ((Dm' ϖ)⁻¹ * !![(1 : K), s; 0, 1] * Dm' ϖ) ↔ ϖ⁻¹ * s ∈ 𝒪 := by
  rw [Dm'_inv_conj hϖ0]
  have hdet : (!![(1 : K), ϖ⁻¹ * s; (ϖ * 0 : K), 1]).det = 1 := by simp [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  constructor
  · intro h; simpa using h.1.1 0 1
  · intro h
    have hinv : (!![(1 : K), ϖ⁻¹ * s; ϖ * 0, 1])⁻¹ = !![(1 : K), -(ϖ⁻¹ * s); 0, 1] := by
      rw [inv_fin_two _ (by rw [hdet]; exact isUnit_one), hdet]; ext i j; fin_cases i <;> fin_cases j <;> simp
    refine ⟨⟨fun i j => ?_, by simp⟩, by rw [hdet]; exact isUnit_one, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [h, one_mem, zero_mem]
    · rw [hinv]; refine ⟨fun i j => ?_, by simp⟩
      fin_cases i <;> fin_cases j <;> simp [h, neg_mem, one_mem, zero_mem]

theorem isB_yRep_inv_mul (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (hk11 : IsU 𝒪 (k 1 1)) :
    IsB 𝒪 ϖ ((yRep ϖ (k 0 1 * (k 1 1)⁻¹))⁻¹ * (k * Dm' ϖ)) := by
  set t := k 0 1 * (k 1 1)⁻¹ with ht
  have htO : t ∈ 𝒪 := mul_mem (hk.1 0 1) hk11.inv.mem

  have hkdet := hk.isU_det
  set k' : Matrix (Fin 2) (Fin 2) K := !![k 0 0 - t * k 1 0, 0; k 1 0, k 1 1] with hk'
  have hUk : !![(1 : K), -t; 0, 1] * k = k' := by
    rw [hk']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hk11.ne_zero] <;> ring
  have hk'det : k'.det = k.det := by
    rw [← hUk, Matrix.det_mul]; simp [Matrix.det_fin_two]
  have hk'00 : IsU 𝒪 (k 0 0 - t * k 1 0) := by

    have e : (k 0 0 - t * k 1 0) = k.det * (k 1 1)⁻¹ := by
      rw [Matrix.det_fin_two, ht]; field_simp [hk11.ne_zero]
    rw [e]; exact hkdet.mul hk11.inv
  have hz : (yRep ϖ t)⁻¹ * (k * Dm' ϖ) = (Dm' ϖ)⁻¹ * k' * Dm' ϖ := by
    rw [yRep_eq hϖ0, Matrix.mul_inv_rev, ← hUk]
    have : (!![(1 : K), t; 0, 1])⁻¹ = !![(1 : K), -t; 0, 1] := by
      rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two]
    rw [this]; simp only [mul_assoc]
  rw [hz]
  have hconj : (Dm' ϖ)⁻¹ * k' * Dm' ϖ = !![k 0 0 - t * k 1 0, 0; ϖ * k 1 0, k 1 1] := by
    rw [Dm'_inv_conj hϖ0, hk']; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hdetZ : (!![k 0 0 - t * k 1 0, 0; ϖ * k 1 0, k 1 1]).det = k.det := by
    rw [← hk'det, hk']; simp [Matrix.det_fin_two]
  rw [hconj]
  refine ⟨⟨fun i j => ?_, by simpa using mul_mem hϖ (hk.1 1 0) |> fun h => by simpa [mul_comm, ← mul_assoc, hϖ0] using hk.1 1 0⟩,
    by rw [hdetZ]; exact hk.2.1, ?_⟩
  · fin_cases i <;> fin_cases j
    · simpa using hk'00.mem
    · simp [zero_mem]
    · simpa using mul_mem hϖ (hk.1 1 0)
    · simpa using hk.1 1 1
  · rw [inv_fin_two _ (by rw [hdetZ]; exact hk.2.1), hdetZ]
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using mul_mem hkdet.inv.mem (hk.1 1 1)
      · simp [zero_mem]
      · simpa using mul_mem hkdet.inv.mem (neg_mem (mul_mem hϖ (hk.1 1 0)))
      · simpa using mul_mem hkdet.inv.mem hk'00.mem
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      have : ϖ⁻¹ * (k.det⁻¹ * -(ϖ * k 1 0)) = -(k.det⁻¹ * k 1 0) := by field_simp
      rw [this]; exact neg_mem (mul_mem hkdet.inv.mem (hk.1 1 0))

theorem IsIntU.mul' {y z : Matrix (Fin 2) (Fin 2) K} (hy : IsIntU 𝒪 y) (hz : IsIntU 𝒪 z) : IsIntU 𝒪 (y * z) := by
  refine ⟨hy.1.mul hz.1, by rw [Matrix.det_mul]; exact hy.2.1.mul hz.2.1, ?_⟩
  rw [Matrix.mul_inv_rev]; exact hz.2.2.mul hy.2.2

theorem IsIntU.inv' {y : Matrix (Fin 2) (Fin 2) K} (hy : IsIntU 𝒪 y) : IsIntU 𝒪 y⁻¹ := by
  refine ⟨hy.2.2, ?_, by rw [Matrix.nonsing_inv_nonsing_inv _ hy.2.1]; exact hy.1⟩
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact hy.2.1.ne_zero.isUnit.inv |> fun h => by simpa using h

theorem isIntU_upper {s : K} (hs : s ∈ 𝒪) : IsIntU 𝒪 !![(1 : K), s; 0, 1] := by
  refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two], ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hs, one_mem, zero_mem]
  · rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, hs, neg_mem, one_mem, zero_mem]

theorem isIntU_lower {s : K} (hs : s ∈ 𝒪) : IsIntU 𝒪 !![(1 : K), 0; s, 1] := by
  refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two], ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hs, one_mem, zero_mem]
  · rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, hs, neg_mem, one_mem, zero_mem]

theorem isIntU_diag {a d : K} (ha : IsU 𝒪 a) (hd : IsU 𝒪 d) : IsIntU 𝒪 (Matrix.diagonal ![a, d]) := by
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha.mem, hd.mem, zero_mem]
  · rw [Matrix.det_diagonal]; simpa using (ha.ne_zero.isUnit.mul hd.ne_zero.isUnit)
  · rw [show (Matrix.diagonal ![a, d])⁻¹ = Matrix.diagonal ![a⁻¹, d⁻¹] from
      Matrix.inv_eq_right_inv (by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [ha.ne_zero, hd.ne_zero])]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha.inv.mem, hd.inv.mem, zero_mem]

theorem isIntU_swap : IsIntU 𝒪 !![(0 : K), 1; 1, 0] := by
  have hdet : (!![(0 : K), 1; 1, 0]).det = -1 := by simp [Matrix.det_fin_two]
  refine ⟨fun i j => ?_, by rw [hdet]; exact isUnit_one.neg, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem]
  · rw [inv_fin_two _ (by rw [hdet]; exact isUnit_one.neg), hdet]
    intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem]

theorem swap_mul_swap : !![(0 : K), 1; 1, 0] * !![(0 : K), 1; 1, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem snf_of_isU00 (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪)
    (m : Matrix (Fin 2) (Fin 2) K) (hmdet : IsUnit m.det)
    (hm1 : IsInt 𝒪 m) (hm2 : IsInt 𝒪 (ϖ • m⁻¹)) (hm3 : ¬ IsInt 𝒪 m⁻¹) (h00 : IsU 𝒪 (m 0 0)) :
    ∃ k₁ k₂ : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k₁ ∧ IsIntU 𝒪 k₂ ∧ m = k₁ * Dm ϖ * k₂ := by
  set a := m 0 0 with ha
  set d := m 1 1 - m 1 0 * a⁻¹ * m 0 1 with hd
  have hdet : m.det = a * d := by rw [Matrix.det_fin_two, hd, ← ha]; field_simp [h00.ne_zero]
  have hdO : d ∈ 𝒪 := sub_mem (hm1 1 1) (mul_mem (mul_mem (hm1 1 0) h00.inv.mem) (hm1 0 1))
  have hd0 : d ≠ 0 := by intro h; apply hmdet.ne_zero; rw [hdet, h, mul_zero]

  set L : Matrix (Fin 2) (Fin 2) K := !![(1 : K), 0; -(m 1 0 * a⁻¹), 1] with hL
  set Rt : Matrix (Fin 2) (Fin 2) K := !![(1 : K), -(a⁻¹ * m 0 1); 0, 1] with hRt
  have hLU : IsIntU 𝒪 L := isIntU_lower (neg_mem (mul_mem (hm1 1 0) h00.inv.mem))
  have hRtU : IsIntU 𝒪 Rt := isIntU_upper (neg_mem (mul_mem h00.inv.mem (hm1 0 1)))
  have hLmR : L * m * Rt = Matrix.diagonal ![a, d] := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [hL, hRt, Matrix.diagonal, ← ha, hd] <;> (try field_simp [h00.ne_zero]) <;> (try ring)

  have hdu : ¬ IsU 𝒪 d := by
    intro hdu
    apply hm3
    have hdiag : IsIntU 𝒪 (Matrix.diagonal ![a, d]) := isIntU_diag h00 hdu
    have : m = L⁻¹ * Matrix.diagonal ![a, d] * Rt⁻¹ := by
      rw [← hLmR]; simp only [← mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hLU.2.1, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hRtU.2.1, mul_one]
    rw [this]; exact ((hLU.inv'.mul' hdiag).mul' hRtU.inv').2.2
  have hϖd : ϖ * d⁻¹ ∈ 𝒪 := by

    have hint : IsInt 𝒪 (Rt⁻¹ * (ϖ • m⁻¹) * L⁻¹) := (hRtU.2.2.mul hm2).mul hLU.2.2
    have e : Rt⁻¹ * (ϖ • m⁻¹) * L⁻¹ = ϖ • (L * m * Rt)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
    rw [e, hLmR, show (Matrix.diagonal ![a, d])⁻¹ = Matrix.diagonal ![a⁻¹, d⁻¹] from
      Matrix.inv_eq_right_inv (by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [h00.ne_zero, hd0])] at hint
    simpa [Matrix.diagonal] using hint 1 1
  have hu : IsU 𝒪 (ϖ⁻¹ * d) :=
    isU_of_mem_of_inv_mem (hmax d hdO hdu) (by rw [_root_.mul_inv_rev, inv_inv, mul_comm]; exact hϖd) (mul_ne_zero (inv_ne_zero hϖ0) hd0)

  have hsplit : Matrix.diagonal ![a, d] = Dm ϖ * Matrix.diagonal ![a, ϖ⁻¹ * d] := by
    rw [Dm, Matrix.diagonal_mul_diagonal]; congr 1; ext i; fin_cases i <;> simp [hϖ0]
  refine ⟨L⁻¹, Matrix.diagonal ![a, ϖ⁻¹ * d] * Rt⁻¹, hLU.inv', (isIntU_diag h00 hu).mul' hRtU.inv', ?_⟩
  rw [mul_assoc, ← mul_assoc (Dm ϖ), ← hsplit, ← hLmR]; simp only [← mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hLU.2.1, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hRtU.2.1, mul_one]

theorem snf (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪)
    (m : Matrix (Fin 2) (Fin 2) K) (hmdet : IsUnit m.det)
    (hm1 : IsInt 𝒪 m) (hm2 : IsInt 𝒪 (ϖ • m⁻¹)) (hm3 : ¬ IsInt 𝒪 m⁻¹) (hm4 : ¬ IsInt 𝒪 (ϖ⁻¹ • m)) :
    ∃ k₁ k₂ : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k₁ ∧ IsIntU 𝒪 k₂ ∧ m = k₁ * Dm ϖ * k₂ := by

  have hex : ∃ i j, IsU 𝒪 (m i j) := by
    by_contra hno
    push_neg at hno
    exact hm4 fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hmax _ (hm1 i j) (hno i j)
  obtain ⟨i, j, hij⟩ := hex
  set σ : Matrix (Fin 2) (Fin 2) K := !![(0 : K), 1; 1, 0] with hσ
  have hσU : IsIntU 𝒪 σ := isIntU_swap
  have hσσ : σ * σ = 1 := swap_mul_swap
  have hσinv : σ⁻¹ = σ := Matrix.inv_eq_right_inv hσσ

  obtain ⟨P, Q, hP, hQ, hPP, hQQ, h00⟩ : ∃ P Q : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 P ∧ IsIntU 𝒪 Q ∧ P * P = 1 ∧ Q * Q = 1 ∧
      IsU 𝒪 ((P * m * Q) 0 0) := by
    have h1U : IsIntU 𝒪 (1 : Matrix (Fin 2) (Fin 2) K) := ⟨IsInt.one, by simp, by rw [inv_one]; exact IsInt.one⟩
    fin_cases i <;> fin_cases j
    · exact ⟨1, 1, h1U, h1U, one_mul 1, one_mul 1, by simpa using hij⟩
    · exact ⟨1, σ, h1U, hσU, one_mul 1, hσσ, by rw [one_mul, Matrix.mul_apply, Fin.sum_univ_two, hσ]; simpa using hij⟩
    · exact ⟨σ, 1, hσU, h1U, hσσ, one_mul 1, by rw [mul_one, Matrix.mul_apply, Fin.sum_univ_two, hσ]; simpa using hij⟩
    · exact ⟨σ, σ, hσU, hσU, hσσ, hσσ, by rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, hσ]; simpa using hij⟩
  have hPinv : P⁻¹ = P := Matrix.inv_eq_right_inv hPP
  have hQinv : Q⁻¹ = Q := Matrix.inv_eq_right_inv hQQ
  set m' := P * m * Q with hm'
  have hm'det : IsUnit m'.det := by rw [hm', Matrix.det_mul, Matrix.det_mul]; exact (hP.2.1.mul hmdet).mul hQ.2.1
  have hm'inv : m'⁻¹ = Q * m⁻¹ * P := by rw [hm', Matrix.mul_inv_rev, Matrix.mul_inv_rev, hPinv, hQinv, mul_assoc]
  have hback : m = P * m' * Q := by
    rw [hm', ← mul_assoc, ← mul_assoc, hPP, one_mul, mul_assoc, hQQ, mul_one]
  have hm'1 : IsInt 𝒪 m' := (hP.1.mul hm1).mul hQ.1
  have hm'2 : IsInt 𝒪 (ϖ • m'⁻¹) := by
    rw [hm'inv, show ϖ • (Q * m⁻¹ * P) = Q * (ϖ • m⁻¹) * P by rw [Matrix.mul_smul, Matrix.smul_mul]]; exact (hQ.1.mul hm2).mul hP.1
  have hm'3 : ¬ IsInt 𝒪 m'⁻¹ := by
    intro h; apply hm3
    have : m⁻¹ = Q * m'⁻¹ * P := by rw [hm'inv, ← mul_assoc, ← mul_assoc, hQQ, one_mul, mul_assoc, hPP, mul_one]
    rw [this]; exact (hQ.1.mul h).mul hP.1
  obtain ⟨k₁, k₂, hk₁, hk₂, hsnf⟩ := snf_of_isU00 hϖ0 hϖ hmax m' hm'det hm'1 hm'2 hm'3 h00
  refine ⟨P * k₁, k₂ * Q, hP.mul' hk₁, hk₂.mul' hQ, ?_⟩
  rw [hback, hsnf]; simp only [mul_assoc]

end pi

section orientedU

variable {K : Type*} [Field K] {𝒪 : ValuationSubring K} {ϖ : K}

theorem isIntU_of_isInt_of_isU_det {k : Matrix (Fin 2) (Fin 2) K} (hk : IsInt 𝒪 k) (hd : IsU 𝒪 k.det) : IsIntU 𝒪 k := by
  have hu : IsUnit k.det := isUnit_iff_ne_zero.mpr hd.ne_zero
  refine ⟨hk, hu, ?_⟩
  rw [inv_fin_two k hu]
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  refine mul_mem hd.inv.mem ?_
  fin_cases i <;> fin_cases j
  · simpa using hk 1 1
  · simpa using neg_mem (hk 0 1)
  · simpa using neg_mem (hk 1 0)
  · simpa using hk 0 0

theorem IsIw.inv_of_isU_det {y : Matrix (Fin 2) (Fin 2) K} (hy : IsIw 𝒪 ϖ y) (hd : IsU 𝒪 y.det) : IsIw 𝒪 ϖ y⁻¹ := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hd.ne_zero
  refine ⟨(isIntU_of_isInt_of_isU_det hy.1 hd).2.2, ?_⟩
  rw [inv_fin_two y hu, Matrix.smul_apply, smul_eq_mul]
  have e : ϖ⁻¹ * (y.det⁻¹ * (!![y 1 1, -y 0 1; -y 1 0, y 0 0] 1 0)) = y.det⁻¹ * -(ϖ⁻¹ * y 1 0) := by
    simp; ring
  rw [e]
  exact mul_mem hd.inv.mem (neg_mem hy.2)

theorem IsIw.mul {A B : Matrix (Fin 2) (Fin 2) K} (hϖ : ϖ ∈ 𝒪) (hA : IsIw 𝒪 ϖ A) (hB : IsIw 𝒪 ϖ B) : IsIw 𝒪 ϖ (A * B) := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e : ϖ⁻¹ * (A 1 0 * B 0 0 + A 1 1 * B 1 0) = (ϖ⁻¹ * A 1 0) * B 0 0 + A 1 1 * (ϖ⁻¹ * B 1 0) := by ring
  rw [e]
  exact add_mem (mul_mem hA.2 (hB.1 0 0)) (mul_mem (hA.1 1 1) hB.2)

theorem IsB.isIw_conj_iff {u : Matrix (Fin 2) (Fin 2) K} (hϖ : ϖ ∈ 𝒪) (hu : IsB 𝒪 ϖ u) (Z : Matrix (Fin 2) (Fin 2) K) :
    IsIw 𝒪 ϖ (u⁻¹ * Z * u) ↔ IsIw 𝒪 ϖ Z := by
  constructor
  · intro h
    have := (hu.1.mul hϖ h).mul hϖ hu.2.2
    rwa [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hu.2.1, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hu.2.1,
      mul_one] at this
  · intro h
    exact (hu.2.2.mul hϖ h).mul hϖ hu.1

theorem isIw_atkinLehner_conj_iff (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsIw 𝒪 ϖ (!![(0 : K), ϖ⁻¹; 1, 0] * Y * !![(0 : K), 1; ϖ, 0]) ↔ IsIw 𝒪 ϖ Y := by
  have e : !![(0 : K), ϖ⁻¹; 1, 0] * Y * !![(0 : K), 1; ϖ, 0] = !![Y 1 1, ϖ⁻¹ * Y 1 0; ϖ * Y 0 1, Y 0 0] := by
    rw [Matrix.eta_fin_two Y, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm, mul_assoc, inv_mul_cancel_left₀ hϖ0, mul_inv_cancel_left₀ hϖ0]
  rw [e]
  constructor
  · rintro ⟨hI, h10⟩
    have h01 : Y 0 1 ∈ 𝒪 := by
      have := h10; simp at this
      rwa [← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul] at this
    refine ⟨fun i j => ?_, by simpa using hI 0 1⟩
    fin_cases i <;> fin_cases j
    · simpa using hI 1 1
    · exact h01
    · have h := hI 0 1; simp at h
      have : Y 1 0 = ϖ * (ϖ⁻¹ * Y 1 0) := by rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
      rw [show (Y : Matrix (Fin 2) (Fin 2) K) ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = Y 1 0 from rfl, this]
      exact mul_mem hϖ h
    · simpa using hI 0 0
  · rintro ⟨hI, h10⟩
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using hI 1 1
      · simpa using h10
      · simpa using mul_mem hϖ (hI 0 1)
      · simpa using hI 0 0
    · simp
      rw [← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
      exact hI 0 1

theorem isU_inv_mul_det_of_clauses (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪)
    {y : Matrix (Fin 2) (Fin 2) K} (hy : IsUnit y.det)
    (h1 : IsIw 𝒪 ϖ y) (h2 : IsIw 𝒪 ϖ (ϖ • y⁻¹)) (h3 : ¬ IsIw 𝒪 ϖ y⁻¹) (h4 : ¬ IsIw 𝒪 ϖ (ϖ⁻¹ • y)) :
    IsU 𝒪 (ϖ⁻¹ * y.det) := by
  have hy0 : y.det ≠ 0 := hy.ne_zero

  have hm3 : ¬ IsInt 𝒪 y⁻¹ := by
    intro hI
    apply h3
    refine h1.inv_of_isU_det (isU_of_mem_of_inv_mem h1.1.det_mem ?_ hy0)
    have : y⁻¹.det = y.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [← this]; exact hI.det_mem
  have hm4 : ¬ IsInt 𝒪 (ϖ⁻¹ • y) := by
    intro hI
    apply h4

    have hw : (ϖ • y⁻¹) * (ϖ⁻¹ • y) = 1 := by
      rw [smul_mul_smul_comm, mul_inv_cancel₀ hϖ0, one_smul, Matrix.nonsing_inv_mul _ hy]
    have hdd : (ϖ • y⁻¹).det * (ϖ⁻¹ • y).det = 1 := by rw [← Matrix.det_mul, hw, Matrix.det_one]
    have hne : (ϖ • y⁻¹).det ≠ 0 := left_ne_zero_of_mul_eq_one hdd
    have hwdet : IsU 𝒪 (ϖ • y⁻¹).det := by
      refine isU_of_mem_of_inv_mem h2.1.det_mem ?_ hne
      rw [← eq_inv_of_mul_eq_one_right hdd]; exact hI.det_mem
    have hinv : (ϖ • y⁻¹)⁻¹ = ϖ⁻¹ • y := Matrix.inv_eq_right_inv hw
    rw [← hinv]
    exact h2.inv_of_isU_det hwdet
  obtain ⟨k₁, k₂, hk₁, hk₂, he⟩ := snf hϖ0 hϖ hmax y hy h1.1 (by
    have := h2.1; exact this) hm3 hm4
  rw [he, Matrix.det_mul, Matrix.det_mul, det_Dm hϖ0]
  have : ϖ⁻¹ * (k₁.det * ϖ * k₂.det) = k₁.det * k₂.det := by field_simp
  rw [this]
  exact hk₁.isU_det.mul hk₂.isU_det

theorem normalFormU (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ)
    (y : Matrix (Fin 2) (Fin 2) K) (hy : IsUnit y.det)
    (h1 : IsIw 𝒪 ϖ y) (h2 : IsIw 𝒪 ϖ (ϖ • y⁻¹)) (h3 : ¬ IsIw 𝒪 ϖ y⁻¹) (h4 : ¬ IsIw 𝒪 ϖ (ϖ⁻¹ • y))
    (h5 : ¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsIw 𝒪 ϖ (y⁻¹ * Y * y) ↔ IsIw 𝒪 ϖ Y)
    (h6 : ¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsIw 𝒪 ϖ Y → IsInt 𝒪 (y⁻¹ * Y * y)) :
    ∃ k : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k ∧ IsU 𝒪 (k 1 1) ∧ y = k * Dm' ϖ := by
  have hdU := isU_inv_mul_det_of_clauses hϖ0 hϖ hmax hy h1 h2 h3 h4
  have hy10 : ϖ⁻¹ * y 1 0 ∈ 𝒪 := h1.2
  have hdet2 : y.det = y 0 0 * y 1 1 - y 0 1 * y 1 0 := Matrix.det_fin_two y
  by_cases hd : IsU 𝒪 (y 1 1)
  ·
    have ha : ¬ IsU 𝒪 (y 0 0) := by
      intro ha

      have hlt : ValuationSubring.valuation 𝒪 (y 0 1 * y 1 0) < ValuationSubring.valuation 𝒪 (y 0 0 * y 1 1) := by
        rw [map_mul, map_mul, ha, hd, mul_one]
        have : y 1 0 = ϖ * (ϖ⁻¹ * y 1 0) := by rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
        rw [this, map_mul]
        calc ValuationSubring.valuation 𝒪 (y 0 1) * (ValuationSubring.valuation 𝒪 ϖ * ValuationSubring.valuation 𝒪 (ϖ⁻¹ * y 1 0))
            ≤ 1 * (ValuationSubring.valuation 𝒪 ϖ * 1) := by
              apply mul_le_mul' (mem_iff_val.mp (h1.1 0 1)) (mul_le_mul' le_rfl (mem_iff_val.mp hy10))
          _ = ValuationSubring.valuation 𝒪 ϖ := by rw [one_mul, mul_one]
          _ < 1 := val_lt_one_of_not_isU hϖ hϖu
      have hdetU : IsU 𝒪 y.det := by
        unfold IsU
        rw [hdet2, Valuation.map_sub_eq_of_lt_left _ hlt, map_mul, ha, hd, mul_one]
      apply hϖu
      have := hdetU.inv.mul (hdU)
      rw [show y.det⁻¹ * (ϖ⁻¹ * y.det) = ϖ⁻¹ by rw [mul_comm ϖ⁻¹ y.det, ← mul_assoc, inv_mul_cancel₀ hy.ne_zero, one_mul]] at this
      simpa using this.inv
    have ha' : ϖ⁻¹ * y 0 0 ∈ 𝒪 := hmax _ (h1.1 0 0) ha
    refine ⟨!![ϖ⁻¹ * y 0 0, y 0 1; ϖ⁻¹ * y 1 0, y 1 1], ?_, by simpa using hd, ?_⟩
    · apply isIntU_of_isInt_of_isU_det
      · intro i j
        fin_cases i <;> fin_cases j
        · simpa using ha'
        · simpa using h1.1 0 1
        · simpa using hy10
        · simpa using h1.1 1 1
      · have : Matrix.det !![ϖ⁻¹ * y 0 0, y 0 1; ϖ⁻¹ * y 1 0, y 1 1] = ϖ⁻¹ * y.det := by
          rw [Matrix.det_fin_two_of, hdet2]; ring
        rw [this]; exact hdU
    · rw [mul_Dm' hϖ0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_inv_cancel_left₀ hϖ0]
  ·
    exfalso
    have hd' : ϖ⁻¹ * y 1 1 ∈ 𝒪 := hmax _ (h1.1 1 1) hd
    by_cases ha : IsU 𝒪 (y 0 0)
    ·
      apply h6
      intro Y hY
      set k' : Matrix (Fin 2) (Fin 2) K := !![y 0 0, y 0 1; ϖ⁻¹ * y 1 0, ϖ⁻¹ * y 1 1] with hk'
      have hyk : y = Dm ϖ * k' := by
        rw [Dm_mul hϖ0]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hk', mul_inv_cancel_left₀ hϖ0]
      have hk'U : IsIntU 𝒪 k' := by
        apply isIntU_of_isInt_of_isU_det
        · intro i j
          fin_cases i <;> fin_cases j
          · simpa [hk'] using h1.1 0 0
          · simpa [hk'] using h1.1 0 1
          · simpa [hk'] using hy10
          · simpa [hk'] using hd'
        · have : k'.det = ϖ⁻¹ * y.det := by rw [hk', Matrix.det_fin_two_of, hdet2]; ring
          rw [this]; exact hdU
      have hDdet : IsUnit (Dm ϖ).det := by rw [det_Dm hϖ0]; exact isUnit_iff_ne_zero.mpr hϖ0
      rw [hyk, Matrix.mul_inv_rev, show k'⁻¹ * (Dm ϖ)⁻¹ * Y * (Dm ϖ * k') = k'⁻¹ * ((Dm ϖ)⁻¹ * Y * Dm ϖ) * k' by
        simp only [mul_assoc], hk'U.isInt_conj_iff]
      exact ((isIw_iff_isInt_and hϖ0 hϖ).mp hY).2
    ·
      apply h5
      intro Y
      have ha' : ϖ⁻¹ * y 0 0 ∈ 𝒪 := hmax _ (h1.1 0 0) ha
      set u : Matrix (Fin 2) (Fin 2) K := !![ϖ⁻¹ * y 1 0, ϖ⁻¹ * y 1 1; y 0 0, y 0 1] with hu
      have hyu : y = !![(0 : K), 1; ϖ, 0] * u := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hu, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel_left₀ hϖ0]
      have huIw : IsIw 𝒪 ϖ u := by
        refine ⟨fun i j => ?_, by simpa [hu] using ha'⟩
        fin_cases i <;> fin_cases j
        · simpa [hu] using hy10
        · simpa [hu] using hd'
        · simpa [hu] using h1.1 0 0
        · simpa [hu] using h1.1 0 1
      have hudet : IsU 𝒪 u.det := by
        have : u.det = -(ϖ⁻¹ * y.det) := by rw [hu, Matrix.det_fin_two_of, hdet2]; ring
        rw [this]; unfold IsU; rw [Valuation.map_neg]; exact hdU
      have huB : IsB 𝒪 ϖ u := ⟨huIw, isUnit_iff_ne_zero.mpr hudet.ne_zero, huIw.inv_of_isU_det hudet⟩
      have hw : (!![(0 : K), 1; ϖ, 0])⁻¹ = !![(0 : K), ϖ⁻¹; 1, 0] := by
        apply Matrix.inv_eq_right_inv
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0]
      rw [hyu, Matrix.mul_inv_rev, hw, show u⁻¹ * !![(0 : K), ϖ⁻¹; 1, 0] * Y * (!![(0 : K), 1; ϖ, 0] * u)
          = u⁻¹ * (!![(0 : K), ϖ⁻¹; 1, 0] * Y * !![(0 : K), 1; ϖ, 0]) * u by simp only [mul_assoc],
        huB.isIw_conj_iff hϖ, isIw_atkinLehner_conj_iff hϖ0 hϖ]

theorem clausesU_of_eq_mul_Dm' (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ)
    {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (hk11 : IsU 𝒪 (k 1 1)) :
    IsIw 𝒪 ϖ (k * Dm' ϖ) ∧ IsIw 𝒪 ϖ (ϖ • (k * Dm' ϖ)⁻¹) ∧ ¬ IsIw 𝒪 ϖ (k * Dm' ϖ)⁻¹ ∧ ¬ IsIw 𝒪 ϖ (ϖ⁻¹ • (k * Dm' ϖ)) ∧
    (¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsIw 𝒪 ϖ ((k * Dm' ϖ)⁻¹ * Y * (k * Dm' ϖ)) ↔ IsIw 𝒪 ϖ Y) ∧
    (¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsIw 𝒪 ϖ Y → IsInt 𝒪 ((k * Dm' ϖ)⁻¹ * Y * (k * Dm' ϖ))) := by
  have hϖinv : ϖ⁻¹ ∉ 𝒪 := fun h => hϖu (isU_of_mem_of_inv_mem hϖ h hϖ0)
  set t : K := k 0 1 * (k 1 1)⁻¹ with ht
  have htO : t ∈ 𝒪 := mul_mem (hk.1 0 1) hk11.inv.mem
  have huB : IsB 𝒪 ϖ ((yRep ϖ t)⁻¹ * (k * Dm' ϖ)) := isB_yRep_inv_mul hϖ0 hϖ hk hk11
  set u := (yRep ϖ t)⁻¹ * (k * Dm' ϖ) with hu
  have hYdet : IsUnit (yRep ϖ t).det := by rw [det_yRep hϖ0]; exact isUnit_iff_ne_zero.mpr hϖ0
  have hyu : k * Dm' ϖ = yRep ϖ t * u := by rw [hu, ← mul_assoc, Matrix.mul_nonsing_inv _ hYdet, one_mul]
  have huU : IsIntU 𝒪 u := ⟨huB.1.1, huB.2.1, huB.2.2.1⟩

  have hE : IsIw 𝒪 ϖ (!![(0 : K), 1; 0, 0]) := ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem], by simp⟩
  have hconjE : (yRep ϖ t)⁻¹ * !![(0 : K), 1; 0, 0] * yRep ϖ t = !![(0 : K), ϖ⁻¹; 0, 0] := by
    rw [yRep_inv hϖ0, yRep]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hnotInt : ¬ IsInt 𝒪 ((k * Dm' ϖ)⁻¹ * !![(0 : K), 1; 0, 0] * (k * Dm' ϖ)) := by
    rw [hyu, Matrix.mul_inv_rev, show u⁻¹ * (yRep ϖ t)⁻¹ * !![(0 : K), 1; 0, 0] * (yRep ϖ t * u)
        = u⁻¹ * ((yRep ϖ t)⁻¹ * !![(0 : K), 1; 0, 0] * yRep ϖ t) * u by simp only [mul_assoc], huU.isInt_conj_iff, hconjE]
    intro h; exact hϖinv (by simpa using h 0 1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hyu]; exact (isIw_yRep hϖ0 hϖ htO).mul hϖ huB.1
  · rw [hyu, Matrix.mul_inv_rev, ← Matrix.mul_smul]
    exact huB.2.2.mul hϖ (isIw_smul_yRep_inv hϖ0 hϖ htO)
  · intro h
    apply not_isIw_yRep_inv hϖ0 hϖ hϖu t
    have := huB.1.mul hϖ h
    rwa [hyu, Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ huB.2.1, one_mul] at this
  · intro h
    apply not_isIw_smul_yRep hϖ0 hϖ hϖu t
    have := h.mul hϖ huB.2.2
    rwa [hyu, smul_mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ huB.2.1, mul_one] at this
  · intro h
    exact hnotInt ((h _).mpr hE).1
  · intro h
    exact hnotInt (h _ hE)

end orientedU

section genericE

open Matrix

variable {K : Type*} [Field K] {𝒪 : ValuationSubring K} {ϖ : K}

theorem IsIw.mul' (hϖ0 : ϖ ≠ 0) {y z : Matrix (Fin 2) (Fin 2) K} (hy : IsIw 𝒪 ϖ y) (hz : IsIw 𝒪 ϖ z) :
    IsIw 𝒪 ϖ (y * z) := by
  refine ⟨hy.1.mul hz.1, ?_⟩
  have e : (y * z) 1 0 = y 1 0 * z 0 0 + y 1 1 * z 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e, mul_add, ← mul_assoc, ← mul_assoc, mul_comm ϖ⁻¹ (y 1 1), mul_assoc (y 1 1)]
  exact add_mem (mul_mem hy.2 (hz.1 0 0)) (mul_mem (hy.1 1 1) hz.2)

theorem IsB.mul' (hϖ0 : ϖ ≠ 0) {y z : Matrix (Fin 2) (Fin 2) K} (hy : IsB 𝒪 ϖ y) (hz : IsB 𝒪 ϖ z) :
    IsB 𝒪 ϖ (y * z) := by
  refine ⟨hy.1.mul' hϖ0 hz.1, by rw [Matrix.det_mul]; exact hy.2.1.mul hz.2.1, ?_⟩
  rw [Matrix.mul_inv_rev]
  exact hz.2.2.mul' hϖ0 hy.2.2

theorem IsB.inv' {z : Matrix (Fin 2) (Fin 2) K} (hz : IsB 𝒪 ϖ z) : IsB 𝒪 ϖ z⁻¹ := by
  refine ⟨hz.2.2, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]; exact hz.2.1.ringInverse
  · rw [Matrix.nonsing_inv_nonsing_inv _ hz.2.1]; exact hz.1

theorem IsB.isIntU {z : Matrix (Fin 2) (Fin 2) K} (hz : IsB 𝒪 ϖ z) : IsIntU 𝒪 z := ⟨hz.1.1, hz.2.1, hz.2.2.1⟩

theorem isB_upper (hϖ0 : ϖ ≠ 0) {s : K} (hs : s ∈ 𝒪) : IsB 𝒪 ϖ !![(1 : K), s; 0, 1] := by
  have hdet : (!![(1 : K), s; 0, 1]).det = 1 := by simp [Matrix.det_fin_two]
  have hinv : (!![(1 : K), s; 0, 1])⁻¹ = !![(1 : K), -s; 0, 1] := by
    rw [inv_fin_two _ (by rw [hdet]; exact isUnit_one), hdet]; ext i j; fin_cases i <;> fin_cases j <;> simp
  refine ⟨⟨fun i j => ?_, by simp⟩, by rw [hdet]; exact isUnit_one, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hs, one_mem, zero_mem]
  · rw [hinv]
    refine ⟨fun i j => ?_, by simp⟩
    fin_cases i <;> fin_cases j <;> simp [hs, neg_mem, one_mem, zero_mem]

theorem upper_mul_yRep (t t' : K) : !![(1 : K), t' - t; 0, 1] * yRep ϖ t = yRep ϖ t' := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [yRep, Matrix.mul_apply, Fin.sum_univ_two]

theorem isU_add_of_lt {x y : K} (hy : IsU 𝒪 y) (hx : 𝒪.valuation x < 1) : IsU 𝒪 (x + y) := by
  unfold IsU at *
  rw [add_comm, Valuation.map_add_eq_of_lt_left]
  · exact hy
  · rw [hy]; exact hx

theorem isU_of_isU_mul_left {x y : K} (hx : x ∈ 𝒪) (hy : y ∈ 𝒪) (h : IsU 𝒪 (x * y)) : IsU 𝒪 x := by
  by_contra hxu
  have hlt := val_lt_one_of_not_isU hx hxu
  unfold IsU at h
  rw [map_mul] at h
  have : 𝒪.valuation x * 𝒪.valuation y < 1 :=
    calc 𝒪.valuation x * 𝒪.valuation y ≤ 𝒪.valuation x * 1 := by gcongr; exact mem_iff_val.mp hy
      _ < 1 := by rw [mul_one]; exact hlt
  exact this.ne h

theorem IsB.isU_one_one (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) {z : Matrix (Fin 2) (Fin 2) K} (hz : IsB 𝒪 ϖ z) :
    IsU 𝒪 (z 1 1) := by

  have h1 : z 1 0 * z⁻¹ 0 1 + z 1 1 * z⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv z hz.2.1) 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hsmall : 𝒪.valuation (z 1 0 * z⁻¹ 0 1) < 1 := by
    rw [map_mul]
    have hz10 : 𝒪.valuation (z 1 0) < 1 := by
      have hmem : ϖ⁻¹ * z 1 0 ∈ 𝒪 := hz.1.2
      have : z 1 0 = ϖ * (ϖ⁻¹ * z 1 0) := by rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
      rw [this, map_mul]
      calc 𝒪.valuation ϖ * 𝒪.valuation (ϖ⁻¹ * z 1 0) ≤ 𝒪.valuation ϖ * 1 := by
            gcongr; exact mem_iff_val.mp hmem
        _ < 1 := by rw [mul_one]; exact val_lt_one_of_not_isU hϖ hϖu
    calc 𝒪.valuation (z 1 0) * 𝒪.valuation (z⁻¹ 0 1) ≤ 𝒪.valuation (z 1 0) * 1 := by
          gcongr; exact mem_iff_val.mp (hz.2.2.1 0 1)
      _ < 1 := by rw [mul_one]; exact hz10

  have hprod : IsU 𝒪 (z 1 1 * z⁻¹ 1 1) := by
    by_contra hnu
    have hlt := val_lt_one_of_not_isU (mul_mem (hz.1.1 1 1) (hz.2.2.1 1 1)) hnu
    have hle := Valuation.map_add_lt 𝒪.valuation hsmall hlt
    rw [h1, map_one] at hle
    exact lt_irrefl _ hle
  exact isU_of_isU_mul_left (hz.1.1 1 1) (hz.2.2.1 1 1) hprod

def wAL (ϖ : K) : Matrix (Fin 2) (Fin 2) K := !![0, 1; ϖ, 0]

theorem det_wAL : (wAL ϖ).det = -ϖ := by simp [wAL, Matrix.det_fin_two]

theorem wAL_inv (hϖ0 : ϖ ≠ 0) : (wAL ϖ)⁻¹ = !![0, ϖ⁻¹; 1, 0] := by
  have hdet : IsUnit (wAL ϖ).det := by rw [det_wAL]; exact (isUnit_iff_ne_zero.mpr hϖ0).neg
  rw [inv_fin_two _ hdet, det_wAL]
  ext i j; fin_cases i <;> fin_cases j <;> simp [wAL] <;> field_simp

theorem wAL_conj (hϖ0 : ϖ ≠ 0) (X : Matrix (Fin 2) (Fin 2) K) :
    wAL ϖ * X * (wAL ϖ)⁻¹ = !![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] := by
  rw [wAL_inv hϖ0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [wAL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> field_simp

theorem IsIw.wconj (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {X : Matrix (Fin 2) (Fin 2) K} (hX : IsIw 𝒪 ϖ X) :
    IsIw 𝒪 ϖ (wAL ϖ * X * (wAL ϖ)⁻¹) := by
  rw [wAL_conj hϖ0]
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j
    · exact hX.1 1 1
    · exact hX.2
    · exact mul_mem hϖ (hX.1 0 1)
    · exact hX.1 0 0
  · show ϖ⁻¹ * (ϖ * X 0 1) ∈ 𝒪
    rw [← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]; exact hX.1 0 1

theorem IsB.wconj (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {X : Matrix (Fin 2) (Fin 2) K} (hX : IsB 𝒪 ϖ X) :
    IsB 𝒪 ϖ (wAL ϖ * X * (wAL ϖ)⁻¹) := by
  have hdetw : IsUnit (wAL ϖ).det := by rw [det_wAL]; exact (isUnit_iff_ne_zero.mpr hϖ0).neg
  refine ⟨hX.1.wconj hϖ0 hϖ, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
    exact (hdetw.mul hX.2.1).mul hdetw.ringInverse
  · have : (wAL ϖ * X * (wAL ϖ)⁻¹)⁻¹ = wAL ϖ * X⁻¹ * (wAL ϖ)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdetw, mul_assoc]
    rw [this]; exact hX.2.2.wconj hϖ0 hϖ

theorem wAL_mul_wAL : wAL ϖ * wAL ϖ = ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wAL, Matrix.mul_apply, Fin.sum_univ_two]

theorem smul_wAL_mul_Dm'_inv_mul_wAL_inv (hϖ0 : ϖ ≠ 0) :
    ϖ • (wAL ϖ * (Dm' ϖ)⁻¹ * (wAL ϖ)⁻¹) = Dm' ϖ := by
  rw [wAL_conj hϖ0, Dm'_inv hϖ0]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dm', Matrix.diagonal] <;> field_simp

theorem Dm'_conj_apply (hϖ0 : ϖ ≠ 0) (B : Matrix (Fin 2) (Fin 2) K) :
    Dm' ϖ * B * (Dm' ϖ)⁻¹ = !![B 0 0, ϖ * B 0 1; ϖ⁻¹ * B 1 0, B 1 1] := by
  rw [Dm'_inv hϖ0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Dm', Matrix.diagonal, Matrix.mul_apply] <;> field_simp

theorem IsIw.isInt_Dm'_conj (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {B : Matrix (Fin 2) (Fin 2) K} (hB : IsIw 𝒪 ϖ B) :
    IsInt 𝒪 (Dm' ϖ * B * (Dm' ϖ)⁻¹) := by
  rw [Dm'_conj_apply hϖ0]
  intro i j; fin_cases i <;> fin_cases j
  · exact hB.1 0 0
  · exact mul_mem hϖ (hB.1 0 1)
  · exact hB.2
  · exact hB.1 1 1

theorem IsB.isIntU_Dm'_conj (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {B : Matrix (Fin 2) (Fin 2) K} (hB : IsB 𝒪 ϖ B) :
    IsIntU 𝒪 (Dm' ϖ * B * (Dm' ϖ)⁻¹) ∧ (Dm' ϖ * B * (Dm' ϖ)⁻¹) 1 1 = B 1 1 := by
  have hdetD : IsUnit (Dm' ϖ).det := by rw [det_Dm' hϖ0]; exact isUnit_iff_ne_zero.mpr hϖ0
  refine ⟨⟨hB.1.isInt_Dm'_conj hϖ0 hϖ, ?_, ?_⟩, by rw [Dm'_conj_apply hϖ0]; simp⟩
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
    exact (hdetD.mul hB.2.1).mul hdetD.ringInverse
  · have : (Dm' ϖ * B * (Dm' ϖ)⁻¹)⁻¹ = Dm' ϖ * B⁻¹ * (Dm' ϖ)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdetD, mul_assoc]
    rw [this]; exact hB.2.2.isInt_Dm'_conj hϖ0 hϖ

theorem IsB.isU_mul_one_one (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) {b k : Matrix (Fin 2) (Fin 2) K}
    (hb : IsB 𝒪 ϖ b) (hk : IsInt 𝒪 k) (hk11 : IsU 𝒪 (k 1 1)) : IsU 𝒪 ((b * k) 1 1) := by
  have e : (b * k) 1 1 = b 1 0 * k 0 1 + b 1 1 * k 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  refine isU_add_of_lt ((hb.isU_one_one hϖ0 hϖ hϖu).mul hk11) ?_
  rw [map_mul]
  have hb10 : 𝒪.valuation (b 1 0) < 1 := by
    have : b 1 0 = ϖ * (ϖ⁻¹ * b 1 0) := by rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
    rw [this, map_mul]
    calc 𝒪.valuation ϖ * 𝒪.valuation (ϖ⁻¹ * b 1 0) ≤ 𝒪.valuation ϖ * 1 := by gcongr; exact mem_iff_val.mp hb.1.2
      _ < 1 := by rw [mul_one]; exact val_lt_one_of_not_isU hϖ hϖu
  calc 𝒪.valuation (b 1 0) * 𝒪.valuation (k 0 1) ≤ 𝒪.valuation (b 1 0) * 1 := by gcongr; exact mem_iff_val.mp (hk 0 1)
    _ < 1 := by rw [mul_one]; exact hb10

end genericE

end F3LOC

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField
open Matrix

namespace F3LOC

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Kv" => HeightOneSpectrum.adicCompletion ℚ v
local notation "Ov" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Dv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

section unif

theorem isU_iff (x : Kv) : IsU (Ov) x ↔ Valued.v x = 1 := by
  constructor
  · intro h
    have h1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp h.mem
    have h2 : Valued.v x⁻¹ ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp h.inv.mem
    rw [map_inv₀] at h2
    have h0 : Valued.v x ≠ 0 := by rw [ne_eq, map_eq_zero]; exact h.ne_zero
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)
  · intro h
    have hx0 : x ≠ 0 := by intro hx; rw [hx, map_zero] at h; exact zero_ne_one h
    refine isU_of_mem_of_inv_mem ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr h.le) ?_ hx0
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

variable (q : ℕ) (hq : q.Prime) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

theorem natCast_mem_Ov : ((q : ℕ) : Kv) ∈ Ov := _root_.natCast_mem _ q

include hq in
theorem natCast_ne_zero' : ((q : ℕ) : Kv) ≠ 0 := by
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective
  exact_mod_cast hq.ne_zero

include hq hqv

theorem valued_natCast_eq_exp_neg_one : Valued.v ((q : ℕ) : Kv) = WithZero.exp (-1 : ℤ) := by
  have hspan : v.asIdeal = Ideal.span {((q : ℕ) : 𝓞 ℚ)} :=
    ((Nat.isMaximal_span_natCast_of_prime hq).eq_of_le v.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hqv)).symm
  have hq0 : ((q : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h1 : ((q : ℕ) : Kv) = algebraMap (𝓞 ℚ) (Kv) ((q : ℕ) : 𝓞 ℚ) := by rw [map_natCast]
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((q : ℕ) : 𝓞 ℚ)
  erw [h2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ hq0 hspan]

theorem not_isU_natCast : ¬ IsU (Ov) ((q : ℕ) : Kv) := by
  rw [isU_iff, valued_natCast_eq_exp_neg_one v q hq hqv]; decide

theorem hmax_natCast (x : Kv) (hx : x ∈ Ov) (hu : ¬ IsU (Ov) x) : ((q : ℕ) : Kv)⁻¹ * x ∈ Ov := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  by_cases hx0 : x = 0
  · rw [hx0, mul_zero, map_zero]; exact zero_le'
  have hV0 : Valued.v x ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨WithZero.log (Valued.v x), (WithZero.exp_log hV0).symm⟩
  have hne : Valued.v x ≠ 1 := by rw [isU_iff] at hu; exact hu
  rw [map_mul, map_inv₀, valued_natCast_eq_exp_neg_one v q hq hqv, hn, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
  rw [hn, ← WithZero.exp_zero, ne_eq, WithZero.exp_inj] at hne
  omega

end unif

section psi

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  (P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

noncomputable def psiP (x : Dv) : Matrix (Fin 2) (Fin 2) Kv := P⁻¹ * φ x * P

variable {P} (hP : IsUnit P.det)
include hP

theorem psiP_mul (x y : Dv) : psiP v φ P (x * y) = psiP v φ P x * psiP v φ P y := by
  unfold psiP; rw [map_mul]; simp only [mul_assoc]; rw [← mul_assoc P P⁻¹, Matrix.mul_nonsing_inv _ hP, one_mul]

theorem psiP_one : psiP v φ P 1 = 1 := by
  unfold psiP; rw [map_one, mul_one, Matrix.nonsing_inv_mul _ hP]

theorem psiP_surj (Y : Matrix (Fin 2) (Fin 2) Kv) : ∃ x : Dv, psiP v φ P x = Y := by
  refine ⟨φ.symm (P * Y * P⁻¹), ?_⟩
  unfold psiP; rw [RingEquiv.apply_symm_apply]; simp only [mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hP, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul _ hP, one_mul]

theorem psiP_injective : Function.Injective (psiP v φ P) := by
  intro x y h
  unfold psiP at h
  have : φ x = φ y := by
    have h' := congrArg (fun Z => P * Z * P⁻¹) h
    simp only [mul_assoc] at h'
    rwa [Matrix.mul_nonsing_inv _ hP, mul_one, mul_one, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hP, one_mul, one_mul] at h'
  exact φ.injective this

theorem psiP_units_inv (g : (Dv)ˣ) : psiP v φ P ((g⁻¹ : (Dv)ˣ) : Dv) = (psiP v φ P (g : Dv))⁻¹ := by
  symm; apply Matrix.inv_eq_left_inv
  rw [← psiP_mul v φ hP, Units.inv_mul, psiP_one v φ hP]

theorem isUnit_det_psiP (g : (Dv)ˣ) : IsUnit (psiP v φ P (g : Dv)).det := by
  apply Matrix.isUnit_det_of_left_inverse (B := psiP v φ P ((g⁻¹ : (Dv)ˣ) : Dv))
  rw [← psiP_mul v φ hP, Units.inv_mul, psiP_one v φ hP]

variable (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
include hφ

theorem psiP_ratSmul (c : ℚ) (x : Dv) : psiP v φ P (c • x) = (c : Kv) • psiP v φ P x := by
  have e : c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : Kv)) * x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, mul_zero]
    | tmul z s =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def,
          eq_ratCast]
    | add x y hx hy => rw [smul_add, mul_add, hx, hy]
  unfold psiP
  rw [e, map_mul, hφ, Matrix.smul_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul]

end psi

section dict

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
  {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) (hq0 : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ≠ 0)
  (hq : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v)

  (hRv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox R v ↔ IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) (psiP v φ P x))
  (hR'v : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
        IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * psiP v φ P x * Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)))

local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)
local notation "ψ" => psiP v φ P
local notation "Sv" => Submodule.localBox (CerednikDrinfeld.meetOrder R n) v

include hR in
theorem isOrder_meetOrder : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) :=
  hR.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n)

include hR hq0 hq hRv hR'v in

theorem mem_Sv_iff (x : Dv) : x ∈ Sv ↔ IsIw (Ov) ϖ (ψ x) := by
  have hRc := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  rw [show CerednikDrinfeld.meetOrder R n = R ⊓ Submodule.conjByFiniteIdele R n from rfl,
    Submodule.localBox_inf R _ hR.fg hR.spanTop hRc.fg hRc.spanTop v, AddSubgroup.mem_inf, hRv, hR'v,
    isIw_iff_isInt_and hq0 hq]

include hR in

private theorem _root_.F3LOC.mem_stabilizer_iff (u : (Dv)ˣ) :
    u ∈ MulAction.stabilizer (Dv)ˣ ((Sv : AddSubgroup (Dv)) : Set (Dv)) ↔ (u : Dv) ∈ Sv ∧ ((u⁻¹ : (Dv)ˣ) : Dv) ∈ Sv := by
  have hS := isOrder_meetOrder hR n
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : (u : Dv) ∈ Sv := by
      have : (u : Dv) • (1 : Dv) ∈ u • ((Sv : AddSubgroup (Dv)) : Set (Dv)) := Set.smul_mem_smul_set (HeckeLocal.one_mem_localBox hS v)
      rw [h] at this; simpa using this
    have h2 : ((u⁻¹ : (Dv)ˣ) : Dv) ∈ Sv := by
      have : (1 : Dv) ∈ u • ((Sv : AddSubgroup (Dv)) : Set (Dv)) := by rw [h]; exact HeckeLocal.one_mem_localBox hS v
      obtain ⟨s, hs, hs1⟩ := this
      have : s = ((u⁻¹ : (Dv)ˣ) : Dv) := by
        simp only [Units.smul_def, smul_eq_mul] at hs1
        calc s = ((u⁻¹ : (Dv)ˣ) : Dv) * ((u : Dv) * s) := by rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = _ := by rw [hs1, mul_one]
      rw [← this]; exact hs
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      simp only [Units.smul_def, smul_eq_mul]; exact HeckeLocal.localBox_mul_mem hS v h1 hs
    · intro s hs
      refine ⟨((u⁻¹ : (Dv)ˣ) : Dv) * s, HeckeLocal.localBox_mul_mem hS v h2 hs, ?_⟩
      simp only [Units.smul_def, smul_eq_mul]; rw [← mul_assoc, Units.mul_inv, one_mul]

p2m_export "F3LOC" "mem_stabilizer_iff"
include hR hq0 hq hRv hR'v hP in

theorem mem_stabilizer_iff_isB (u : (Dv)ˣ) :
    u ∈ MulAction.stabilizer (Dv)ˣ ((Sv : AddSubgroup (Dv)) : Set (Dv)) ↔ IsB (Ov) ϖ (ψ (u : Dv)) := by
  rw [mem_stabilizer_iff v hR n u, mem_Sv_iff v φ hR n q hq0 hq hRv hR'v, mem_Sv_iff v φ hR n q hq0 hq hRv hR'v,
    psiP_units_inv v φ hP, IsB]
  exact ⟨fun h => ⟨h.1, isUnit_det_psiP v φ hP u, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

include hq0 hq hRv hR'v hP hφ hR in

theorem clause_i_iff (g : (Dv)ˣ) :
    ((g : Dv) ∈ Sv ∧ (q : ℚ) • ((g⁻¹ : (Dv)ˣ) : Dv) ∈ Sv ∧ ((g⁻¹ : (Dv)ˣ) : Dv) ∉ Sv ∧ (q : ℚ)⁻¹ • (g : Dv) ∉ Sv) ↔
      (IsIw (Ov) ϖ (ψ g) ∧ IsIw (Ov) ϖ (ϖ • (ψ g)⁻¹) ∧ ¬ IsIw (Ov) ϖ (ψ g)⁻¹ ∧ ¬ IsIw (Ov) ϖ (ϖ⁻¹ • ψ g)) := by
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective
  simp only [mem_Sv_iff v φ hR n q hq0 hq hRv hR'v, psiP_ratSmul v φ hP hφ, psiP_units_inv v φ hP, Rat.cast_inv,
    Rat.cast_natCast]

include hq0 hRv hR'v hP in

theorem clause_ii_iff (g : (Dv)ˣ) :
    (∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : Dv) * x * g ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔ x ∈ Submodule.localBox R v) ↔
      (∀ Y : Matrix (Fin 2) (Fin 2) Kv, IsInt (Ov) ((Dm ϖ)⁻¹ * ((ψ g)⁻¹ * Y * ψ g) * Dm ϖ) ↔ IsInt (Ov) Y) := by
  constructor
  · intro h Y
    obtain ⟨x, rfl⟩ := psiP_surj v φ hP Y
    rw [← hRv x, ← h x, hR'v, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]
  · intro h x
    rw [hR'v, hRv, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]
    exact h _

include hq0 hRv hR'v hP in

theorem clause_iii_iff (g : (Dv)ˣ) :
    (¬ ∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : Dv) * x * g ∈ Submodule.localBox R v ↔ x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v) ↔
      (¬ ∀ Y : Matrix (Fin 2) (Fin 2) Kv, IsInt (Ov) ((ψ g)⁻¹ * Y * ψ g) ↔ IsInt (Ov) ((Dm ϖ)⁻¹ * Y * Dm ϖ)) := by
  refine not_congr ⟨fun h Y => ?_, fun h x => ?_⟩
  · obtain ⟨x, rfl⟩ := psiP_surj v φ hP Y
    rw [← psiP_units_inv v φ hP, ← psiP_mul v φ hP, ← psiP_mul v φ hP, ← hRv, ← hR'v]; exact h x
  · rw [hRv, hR'v, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]; exact h _

end dict

section unitOf

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
include hP

noncomputable def unitOf (Y : Matrix (Fin 2) (Fin 2) Kv) (hY : IsUnit Y.det) : (Dv)ˣ where
  val := φ.symm (P * Y * P⁻¹)
  inv := φ.symm (P * Y⁻¹ * P⁻¹)
  val_inv := by
    rw [← map_mul, show P * Y * P⁻¹ * (P * Y⁻¹ * P⁻¹) = 1 by
      rw [show P * Y * P⁻¹ * (P * Y⁻¹ * P⁻¹) = P * (Y * (P⁻¹ * P) * Y⁻¹) * P⁻¹ by simp only [mul_assoc],
        Matrix.nonsing_inv_mul _ hP, mul_one, Matrix.mul_nonsing_inv _ hY, mul_one, Matrix.mul_nonsing_inv _ hP], map_one]
  inv_val := by
    rw [← map_mul, show P * Y⁻¹ * P⁻¹ * (P * Y * P⁻¹) = 1 by
      rw [show P * Y⁻¹ * P⁻¹ * (P * Y * P⁻¹) = P * (Y⁻¹ * (P⁻¹ * P) * Y) * P⁻¹ by simp only [mul_assoc],
        Matrix.nonsing_inv_mul _ hP, mul_one, Matrix.nonsing_inv_mul _ hY, mul_one, Matrix.mul_nonsing_inv _ hP], map_one]

theorem psiP_unitOf (Y : Matrix (Fin 2) (Fin 2) Kv) (hY : IsUnit Y.det) : psiP v φ P (unitOf v φ hP Y hY : Dv) = Y := by
  show P⁻¹ * φ (φ.symm (P * Y * P⁻¹)) * P = Y
  rw [RingEquiv.apply_symm_apply]; simp only [mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hP, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul _ hP, one_mul]

end unitOf

theorem mem_localBox_conj_iff' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : Dv) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ g) v ↔
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) * x *
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : _) ∈ Submodule.localBox Λ v := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff (D := ℍ[ℚ, a, b]) Λ hΛ.fg hΛ.spanTop g v x]
  have hgi : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : _) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hgi' : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : _) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← mul_assoc, ← mul_assoc, hgi, one_mul, mul_assoc, hgi, mul_one]; exact hy
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, ← mul_assoc, hgi', one_mul, mul_assoc, hgi', mul_one]⟩

section dictU

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
  {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) (hq0 : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ≠ 0)
  (hq : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v)
  (hRv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox R v ↔ IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) (psiP v φ P x))
  (hR'v : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
        IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * psiP v φ P x * Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)))

local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)
local notation "ψ" => psiP v φ P
local notation "Sv" => Submodule.localBox (CerednikDrinfeld.meetOrder R n) v

include hR hq0 hq hRv hR'v hP in

theorem clause_v_iff (g : (Dv)ˣ) :
    (¬ ∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : Dv) * x * g ∈ Sv ↔ x ∈ Sv) ↔
      (¬ ∀ Y : Matrix (Fin 2) (Fin 2) Kv, IsIw (Ov) ϖ ((ψ g)⁻¹ * Y * ψ g) ↔ IsIw (Ov) ϖ Y) := by
  refine not_congr ⟨fun h Y => ?_, fun h x => ?_⟩
  · obtain ⟨x, rfl⟩ := psiP_surj v φ hP Y
    rw [← psiP_units_inv v φ hP, ← psiP_mul v φ hP, ← psiP_mul v φ hP, ← mem_Sv_iff v φ hR n q hq0 hq hRv hR'v,
      ← mem_Sv_iff v φ hR n q hq0 hq hRv hR'v]
    exact h x
  · rw [mem_Sv_iff v φ hR n q hq0 hq hRv hR'v, mem_Sv_iff v φ hR n q hq0 hq hRv hR'v, psiP_mul v φ hP, psiP_mul v φ hP,
      psiP_units_inv v φ hP]
    exact h _

include hR hq0 hq hRv hR'v hP in

theorem clause_vi_iff (g : (Dv)ˣ) :
    (¬ ∀ x : Dv, x ∈ Sv → ((g⁻¹ : (Dv)ˣ) : Dv) * x * g ∈ Submodule.localBox R v) ↔
      (¬ ∀ Y : Matrix (Fin 2) (Fin 2) Kv, IsIw (Ov) ϖ Y → IsInt (Ov) ((ψ g)⁻¹ * Y * ψ g)) := by
  refine not_congr ⟨fun h Y hY => ?_, fun h x hx => ?_⟩
  · obtain ⟨x, rfl⟩ := psiP_surj v φ hP Y
    rw [← psiP_units_inv v φ hP, ← psiP_mul v φ hP, ← psiP_mul v φ hP, ← hRv]
    exact h x ((mem_Sv_iff v φ hR n q hq0 hq hRv hR'v x).mpr hY)
  · rw [hRv, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]
    exact h _ ((mem_Sv_iff v φ hR n q hq0 hq hRv hR'v x).mp hx)

end dictU

section indicesE

set_option synthInstance.maxHeartbeats 400000

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
  (q : ℕ) (hq0 : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ≠ 0)
  (hqO : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v)
  (hϖu : ¬ IsU (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))
  (H : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ)
  (hmemH : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ,
    u ∈ H ↔ IsB (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)
      (psiP v φ P (u : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)))

local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)
local notation "ψ" => psiP v φ P

def NF (x : (Dv)ˣ) : Prop :=
  ∃ k : Matrix (Fin 2) (Fin 2) Kv, IsIntU (Ov) k ∧ IsU (Ov) (k 1 1) ∧ ψ (x : Dv) = k * Dm' ϖ

include hP in
omit hq0 hqO hϖu hmemH in

theorem units_eq_of_psiP_eq {x y : (Dv)ˣ} (h : ψ (x : Dv) = ψ (y : Dv)) : x = y :=
  Units.ext (psiP_injective v φ hP h)

noncomputable def zE : (Dv)ˣ :=
  unitOf v φ hP (Dm ϖ * Dm' ϖ)
    (by rw [Matrix.det_mul, det_Dm hq0, det_Dm' hq0]; exact (mul_ne_zero hq0 hq0).isUnit)

omit hP in
theorem Dm_mul_Dm' : Dm ϖ * Dm' ϖ = ϖ • (1 : Matrix (Fin 2) (Fin 2) Kv) := by
  rw [Dm, Dm', Matrix.diagonal_mul_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply]

noncomputable def WE : (Dv)ˣ :=
  unitOf v φ hP (wAL ϖ) (by rw [det_wAL]; exact hq0.isUnit.neg)

noncomputable def dE : (Dv)ˣ :=
  unitOf v φ hP (Dm' ϖ) (by rw [det_Dm' hq0]; exact hq0.isUnit)

include hP

omit hqO hϖu hmemH in
theorem psiP_zE : ψ (zE v φ hP q hq0 : Dv) = ϖ • (1 : Matrix (Fin 2) (Fin 2) Kv) := by
  rw [← Dm_mul_Dm']; exact psiP_unitOf v φ hP _ _
omit hqO hϖu hmemH in
theorem psiP_WE : ψ (WE v φ hP q hq0 : Dv) = wAL ϖ := psiP_unitOf v φ hP _ _
omit hqO hϖu hmemH in
theorem psiP_dE : ψ (dE v φ hP q hq0 : Dv) = Dm' ϖ := psiP_unitOf v φ hP _ _

omit hqO hϖu hmemH in

theorem zE_comm (x : (Dv)ˣ) : zE v φ hP q hq0 * x = x * zE v φ hP q hq0 := by
  apply units_eq_of_psiP_eq v φ hP
  rw [Units.val_mul, Units.val_mul, psiP_mul v φ hP, psiP_mul v φ hP, psiP_zE, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one]

omit hqO hϖu hmemH in

theorem WE_mul_WE : WE v φ hP q hq0 * WE v φ hP q hq0 = zE v φ hP q hq0 := by
  apply units_eq_of_psiP_eq v φ hP
  rw [Units.val_mul, psiP_mul v φ hP, psiP_WE, psiP_zE, wAL_mul_wAL]

omit hqO hϖu hmemH in

theorem WE_conj_dE_inv : WE v φ hP q hq0 * (dE v φ hP q hq0)⁻¹ * (WE v φ hP q hq0)⁻¹ * zE v φ hP q hq0 =
    dE v φ hP q hq0 := by
  apply units_eq_of_psiP_eq v φ hP
  rw [Units.val_mul, Units.val_mul, Units.val_mul, psiP_mul v φ hP, psiP_mul v φ hP, psiP_mul v φ hP,
    psiP_units_inv v φ hP, psiP_units_inv v φ hP, psiP_WE, psiP_dE, psiP_zE, Matrix.mul_smul, mul_one,
    smul_wAL_mul_Dm'_inv_mul_wAL_inv hq0]

include hqO hmemH in
omit hϖu in

theorem WE_conj_mem {k : (Dv)ˣ} (hk : k ∈ H) : WE v φ hP q hq0 * k * (WE v φ hP q hq0)⁻¹ ∈ H := by
  rw [hmemH] at hk ⊢
  rw [Units.val_mul, Units.val_mul, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP, psiP_WE]
  exact hk.wconj hq0 hqO

include hqO hmemH in
omit hϖu in

theorem WE_inv_conj_mem {k : (Dv)ˣ} (hk : k ∈ H) : (WE v φ hP q hq0)⁻¹ * k * WE v φ hP q hq0 ∈ H := by
  have hWW := WE_mul_WE v φ hP q hq0
  have key : (WE v φ hP q hq0)⁻¹ * k * WE v φ hP q hq0 =
      (WE v φ hP q hq0 * WE v φ hP q hq0)⁻¹ * (WE v φ hP q hq0 * k * (WE v φ hP q hq0)⁻¹) *
        (WE v φ hP q hq0 * WE v φ hP q hq0) := by group
  rw [key, hWW, mul_assoc, ← zE_comm v φ hP q hq0, inv_mul_cancel_left]
  exact WE_conj_mem v φ hP q hq0 hqO H hmemH hk

include hqO hϖu hmemH in

theorem nf_iff_exists (x : (Dv)ˣ) :
    NF v φ (P := P) q x ↔ ∃ h₁ ∈ H, ∃ h₂ ∈ H, x = h₁ * dE v φ hP q hq0 * h₂ := by
  have hdetD : IsUnit (Dm' ϖ).det := by rw [det_Dm' hq0]; exact hq0.isUnit
  constructor
  · rintro ⟨k, hk, hk11, hx⟩
    set t₀ : Kv := k 0 1 * (k 1 1)⁻¹ with ht₀
    have ht₀O : t₀ ∈ Ov := mul_mem (hk.1 0 1) hk11.inv.mem
    have hb₀ : IsB (Ov) ϖ ((yRep ϖ t₀)⁻¹ * (k * Dm' ϖ)) := isB_yRep_inv_mul hq0 hqO hk hk11
    have hN : IsB (Ov) ϖ !![(1 : Kv), t₀; 0, 1] := isB_upper hq0 ht₀O
    have hYdet : IsUnit (yRep ϖ t₀).det := by rw [det_yRep hq0]; exact hq0.isUnit
    refine ⟨unitOf v φ hP _ hN.2.1, (hmemH _).mpr (by rw [psiP_unitOf]; exact hN),
      unitOf v φ hP _ hb₀.2.1, (hmemH _).mpr (by rw [psiP_unitOf]; exact hb₀), ?_⟩
    apply units_eq_of_psiP_eq v φ hP
    rw [Units.val_mul, Units.val_mul, psiP_mul v φ hP, psiP_mul v φ hP, psiP_unitOf, psiP_unitOf, psiP_dE, hx,
      ← yRep_eq hq0, Matrix.mul_nonsing_inv_cancel_left _ _ hYdet]
  · rintro ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    have hB₁ := (hmemH h₁).mp hh₁
    have hB₂ := (hmemH h₂).mp hh₂
    obtain ⟨hconj, h11⟩ := hB₂.isIntU_Dm'_conj hq0 hqO
    refine ⟨ψ (h₁ : Dv) * (Dm' ϖ * ψ (h₂ : Dv) * (Dm' ϖ)⁻¹), hB₁.isIntU.mul' hconj, ?_, ?_⟩
    · have := IsB.isU_mul_one_one hq0 hqO hϖu hB₁ hconj.1 (by rw [h11]; exact hB₂.isU_one_one hq0 hqO hϖu)
      exact this
    · rw [Units.val_mul, Units.val_mul, psiP_mul v φ hP, psiP_mul v φ hP, psiP_dE]
      simp only [mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hdetD, mul_one]

omit hqO hϖu hmemH hP in

theorem dc_iff_of_eq {g d h₁ h₂ : (Dv)ˣ} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) (hg : g = h₁ * d * h₂) (c : (Dv)ˣ ⧸ H) :
    (∃ k ∈ H, (QuotientGroup.mk (k * g) : (Dv)ˣ ⧸ H) = c) ↔ (∃ k ∈ H, (QuotientGroup.mk (k * d) : (Dv)ˣ ⧸ H) = c) := by
  subst hg
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * h₁, H.mul_mem hk hh₁, ?_⟩
    rw [QuotientGroup.eq]
    have : (k * h₁ * d)⁻¹ * (k * (h₁ * d * h₂)) = h₂ := by group
    rw [this]; exact hh₂
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * h₁⁻¹, H.mul_mem hk (H.inv_mem hh₁), ?_⟩
    rw [QuotientGroup.eq]
    have : (k * h₁⁻¹ * (h₁ * d * h₂))⁻¹ * (k * d) = h₂⁻¹ := by group
    rw [this]; exact H.inv_mem hh₂

include hqO hϖu hmemH in

theorem nf_iff_dc (c : (Dv)ˣ ⧸ H) :
    (∃ x, NF v φ (P := P) q x ∧ (QuotientGroup.mk x : (Dv)ˣ ⧸ H) = c) ↔
      (∃ k ∈ H, (QuotientGroup.mk (k * dE v φ hP q hq0) : (Dv)ˣ ⧸ H) = c) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (nf_iff_exists v φ hP q hq0 hqO hϖu H hmemH _).mp hx
    refine ⟨h₁, hh₁, ?_⟩
    rw [QuotientGroup.eq]
    have : (h₁ * dE v φ hP q hq0)⁻¹ * (h₁ * dE v φ hP q hq0 * h₂) = h₂ := by group
    rw [this]; exact hh₂
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * dE v φ hP q hq0, (nf_iff_exists v φ hP q hq0 hqO hϖu H hmemH _).mpr ⟨k, hk, 1, H.one_mem, by group⟩, rfl⟩

omit hϖu in
include hqO hmemH in

theorem WE_inv_conj_dE : (WE v φ hP q hq0)⁻¹ * dE v φ hP q hq0 * WE v φ hP q hq0 * (zE v φ hP q hq0)⁻¹ =
    (dE v φ hP q hq0)⁻¹ := by
  have h := WE_conj_dE_inv v φ hP q hq0
  have hz := zE_comm v φ hP q hq0 (WE v φ hP q hq0)⁻¹
  have h' : WE v φ hP q hq0 * (dE v φ hP q hq0)⁻¹ * zE v φ hP q hq0 * (WE v φ hP q hq0)⁻¹ = dE v φ hP q hq0 := by
    rw [mul_assoc (WE v φ hP q hq0 * (dE v φ hP q hq0)⁻¹), hz, ← mul_assoc]; exact h
  calc (WE v φ hP q hq0)⁻¹ * dE v φ hP q hq0 * WE v φ hP q hq0 * (zE v φ hP q hq0)⁻¹
      = (WE v φ hP q hq0)⁻¹ * (WE v φ hP q hq0 * (dE v φ hP q hq0)⁻¹ * zE v φ hP q hq0 * (WE v φ hP q hq0)⁻¹) *
          WE v φ hP q hq0 * (zE v φ hP q hq0)⁻¹ := by rw [h']
    _ = (dE v φ hP q hq0)⁻¹ := by group

omit hϖu in
include hqO hmemH in

theorem natCard_dc_inv_eq :
    Nat.card {c : (Dv)ˣ ⧸ H // ∃ k ∈ H, (QuotientGroup.mk (k * (dE v φ hP q hq0)⁻¹) : (Dv)ˣ ⧸ H) = c} =
      Nat.card {c : (Dv)ˣ ⧸ H // ∃ k ∈ H, (QuotientGroup.mk (k * dE v φ hP q hq0) : (Dv)ˣ ⧸ H) = c} := by
  set W := WE v φ hP q hq0 with hWdef
  set z := zE v φ hP q hq0 with hzdef
  set d := dE v φ hP q hq0 with hddef
  have hz : ∀ x : (Dv)ˣ, z * x = x * z := zE_comm v φ hP q hq0
  have hz' : ∀ x : (Dv)ˣ, z⁻¹ * x = x * z⁻¹ := fun x => by
    rw [eq_comm, mul_inv_eq_iff_eq_mul, mul_assoc, ← hz x, inv_mul_cancel_left]

  have compat₁ : ∀ x y : (Dv)ˣ, x⁻¹ * y ∈ H → (W * x * W⁻¹ * z)⁻¹ * (W * y * W⁻¹ * z) ∈ H := by
    intro x y hxy
    have : (W * x * W⁻¹ * z)⁻¹ * (W * y * W⁻¹ * z) = z⁻¹ * (W * (x⁻¹ * y) * W⁻¹) * z := by group
    rw [this, mul_assoc, ← hz, inv_mul_cancel_left]
    exact WE_conj_mem v φ hP q hq0 hqO H hmemH hxy
  have compat₂ : ∀ x y : (Dv)ˣ, x⁻¹ * y ∈ H → (W⁻¹ * x * W * z⁻¹)⁻¹ * (W⁻¹ * y * W * z⁻¹) ∈ H := by
    intro x y hxy
    have : (W⁻¹ * x * W * z⁻¹)⁻¹ * (W⁻¹ * y * W * z⁻¹) = z * (W⁻¹ * (x⁻¹ * y) * W) * z⁻¹ := by group
    rw [this, mul_assoc, ← hz', ← mul_assoc, mul_inv_cancel, one_mul]
    exact WE_inv_conj_mem v φ hP q hq0 hqO H hmemH hxy
  let Φ : (Dv)ˣ ⧸ H → (Dv)ˣ ⧸ H :=
    Quotient.map' (fun x => W * x * W⁻¹ * z) (fun x y hxy =>
      QuotientGroup.leftRel_apply.mpr (compat₁ x y (QuotientGroup.leftRel_apply.mp hxy)))
  let Ψ : (Dv)ˣ ⧸ H → (Dv)ˣ ⧸ H :=
    Quotient.map' (fun x => W⁻¹ * x * W * z⁻¹) (fun x y hxy =>
      QuotientGroup.leftRel_apply.mpr (compat₂ x y (QuotientGroup.leftRel_apply.mp hxy)))
  have hΦ : ∀ x : (Dv)ˣ, Φ (QuotientGroup.mk x) = QuotientGroup.mk (W * x * W⁻¹ * z) := fun x => rfl
  have hΨ : ∀ x : (Dv)ˣ, Ψ (QuotientGroup.mk x) = QuotientGroup.mk (W⁻¹ * x * W * z⁻¹) := fun x => rfl
  have hΨΦ : ∀ c, Ψ (Φ c) = c := by
    intro c; induction c using QuotientGroup.induction_on with
    | H x =>
      rw [hΦ, hΨ]
      congr 1
      have : W⁻¹ * (W * x * W⁻¹ * z) * W * z⁻¹ = x * (W⁻¹ * (z * W) * z⁻¹) := by group
      rw [this, hz, ← mul_assoc W⁻¹, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one]
  have hΦΨ : ∀ c, Φ (Ψ c) = c := by
    intro c; induction c using QuotientGroup.induction_on with
    | H x =>
      rw [hΨ, hΦ]
      congr 1
      have : W * (W⁻¹ * x * W * z⁻¹) * W⁻¹ * z = x * (W * z⁻¹ * W⁻¹) * z := by group
      have hWz : W * z⁻¹ * W⁻¹ = z⁻¹ := by rw [← hz' W, mul_inv_cancel_right]
      rw [this, hWz, mul_assoc, inv_mul_cancel, mul_one]
  let e : (Dv)ˣ ⧸ H ≃ (Dv)ˣ ⧸ H := ⟨Φ, Ψ, hΨΦ, hΦΨ⟩
  refine Nat.card_congr (e.subtypeEquiv fun c => ?_)

  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨W * k * W⁻¹, WE_conj_mem v φ hP q hq0 hqO H hmemH hk, ?_⟩
    rw [show e (QuotientGroup.mk (k * d⁻¹)) = Φ (QuotientGroup.mk (k * d⁻¹)) from rfl, hΦ]
    congr 1
    have : W * (k * d⁻¹) * W⁻¹ * z = W * k * W⁻¹ * (W * d⁻¹ * W⁻¹ * z) := by group
    rw [this, hWdef, hddef, hzdef, WE_conj_dE_inv v φ hP q hq0]
  · rintro ⟨k, hk, hkc⟩
    refine ⟨W⁻¹ * k * W, WE_inv_conj_mem v φ hP q hq0 hqO H hmemH hk, ?_⟩
    have hc : c = Ψ (e c) := (hΨΦ c).symm
    rw [hc, show e c = QuotientGroup.mk (k * d) from hkc.symm, hΨ]
    congr 1
    have : W⁻¹ * (k * d) * W * z⁻¹ = W⁻¹ * k * W * (W⁻¹ * d * W * z⁻¹) := by group
    rw [this, hWdef, hddef, hzdef, WE_inv_conj_dE v φ hP q hq0 hqO H hmemH]

include hP hq0 hqO hϖu hmemH in

theorem indicesU
    (hcount : Nat.card {c : (Dv)ˣ ⧸ H // ∃ x, NF v φ (P := P) q x ∧ (QuotientGroup.mk x : (Dv)ˣ ⧸ H) = c} = q)
    (g : (Dv)ˣ) (hg : NF v φ (P := P) q g) :
    (H ⊓ H.map (MulAut.conj g).toMonoidHom).relIndex H = q ∧
      (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom).relIndex H = q := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hgd⟩ := (nf_iff_exists v φ hP q hq0 hqO hϖu H hmemH g).mp hg
  have hd : Nat.card {c : (Dv)ˣ ⧸ H // ∃ k ∈ H, (QuotientGroup.mk (k * dE v φ hP q hq0) : (Dv)ˣ ⧸ H) = c} = q := by
    exact (Nat.card_congr (Equiv.subtypeEquivRight fun c => (nf_iff_dc v φ hP q hq0 hqO hϖu H hmemH c).symm)).trans hcount
  constructor
  · rw [Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq,
      Nat.card_congr (Equiv.subtypeEquivRight fun c => dc_iff_of_eq v H hh₁ hh₂ hgd c), hd]
  · have hgd' : g⁻¹ = h₂⁻¹ * (dE v φ hP q hq0)⁻¹ * h₁⁻¹ := by rw [hgd]; group
    rw [Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq,
      Nat.card_congr (Equiv.subtypeEquivRight fun c => dc_iff_of_eq v H (H.inv_mem hh₂) (H.inv_mem hh₁) hgd' c),
      natCard_dc_inv_eq v φ hP q hq0 hqO H hmemH, hd]

end indicesE

section mainU

theorem mainU
    (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
    (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) (hq : q.Prime) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hRv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox R v ↔ IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) (psiP v φ P x))
    (hR'v : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
        IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * psiP v φ P x * Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))) :
    Nat.card {c : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) //
        ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ,
          (((g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔ z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v, z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v →
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox R v)) ∧
          (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v))) = c} = q ∧
    ∀ g : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ,
      (((g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔ z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v, z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v →
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ∈ Submodule.localBox R v)) →
        (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) ⊓ (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v))).map (MulAut.conj g).toMonoidHom).relIndex (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v))) = q ∧
        (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) ⊓ (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v))).map (MulAut.conj g⁻¹).toMonoidHom).relIndex (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v))) = q  := by
  classical
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective
  have hϖ0 : ((q : ℕ) : Kv) ≠ 0 := natCast_ne_zero' v q hq
  have hϖO : ((q : ℕ) : Kv) ∈ Ov := natCast_mem_Ov v q
  have hϖu : ¬ IsU (Ov) ((q : ℕ) : Kv) := not_isU_natCast v q hq hqv
  have hmax := hmax_natCast v q hq hqv

  set H := MulAction.stabilizer (Dv)ˣ ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (Dv)) : Set (Dv)) with hH
  have hmemH : ∀ u : (Dv)ˣ, u ∈ H ↔ IsB (Ov) ((q : ℕ) : Kv) (psiP v φ P (u : Dv)) :=
    fun u => mem_stabilizer_iff_isB v φ hP hRo n q hϖ0 hϖO hRv hR'v u
  have hclause_i := clause_i_iff v φ hP hφ hRo n q hϖ0 hϖO hRv hR'v
  have hclause_v := clause_v_iff v φ hP hRo n q hϖ0 hϖO hRv hR'v
  have hclause_vi := clause_vi_iff v φ hP hRo n q hϖ0 hϖO hRv hR'v

  have hYdet : ∀ t : Kv, IsUnit (yRep ((q : ℕ) : Kv) t).det := fun t => by rw [det_yRep hϖ0]; exact hϖ0.isUnit
  let gRep : Ov → (Dv)ˣ := fun t => unitOf v φ hP (yRep ((q : ℕ) : Kv) (t : Kv)) (hYdet _)
  have hgRep : ∀ t : Ov, psiP v φ P (gRep t : Dv) = yRep ((q : ℕ) : Kv) (t : Kv) := fun t => psiP_unitOf v φ hP _ _
  let F : Ov → (Dv)ˣ ⧸ H := fun t => (gRep t : (Dv)ˣ ⧸ H)

  have hker : ∀ s t : Ov, F s = F t ↔ ((q : ℕ) : Kv)⁻¹ * ((t : Kv) - (s : Kv)) ∈ Ov := by
    intro s t
    show ((gRep s : (Dv)ˣ ⧸ H)) = (gRep t : (Dv)ˣ ⧸ H) ↔ _
    rw [QuotientGroup.eq, hmemH, Units.val_mul, psiP_mul v φ hP, psiP_units_inv v φ hP, hgRep, hgRep,
      yRep_eq hϖ0, yRep_eq hϖ0, Matrix.mul_inv_rev,
      show (Dm' ((q : ℕ) : Kv))⁻¹ * (!![(1 : Kv), (s : Kv); 0, 1])⁻¹ * (!![(1 : Kv), (t : Kv); 0, 1] * Dm' ((q : ℕ) : Kv))
        = (Dm' ((q : ℕ) : Kv))⁻¹ * ((!![(1 : Kv), (s : Kv); 0, 1])⁻¹ * !![(1 : Kv), (t : Kv); 0, 1]) * Dm' ((q : ℕ) : Kv) by simp only [mul_assoc],
      show (!![(1 : Kv), (s : Kv); 0, 1])⁻¹ * !![(1 : Kv), (t : Kv); 0, 1] = !![(1 : Kv), (t : Kv) - (s : Kv); 0, 1] by
        rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, Matrix.mul_apply] <;> ring]
    exact isB_conj_unipotent_iff hϖ0 (sub_mem t.2 s.2)

  have hyRepk : ∀ t : Ov, yRep ((q : ℕ) : Kv) (t : Kv) = !![(1 : Kv), (t : Kv); 0, 1] * Dm' ((q : ℕ) : Kv) := fun t => yRep_eq hϖ0 _
  have hrange : Set.range F = {c : (Dv)ˣ ⧸ H | ∃ g : (Dv)ˣ,
        ((((g : Dv) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ) • ((g⁻¹ : (Dv)ˣ) : Dv) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            ((g⁻¹ : (Dv)ˣ) : Dv) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ)⁻¹ • (g : Dv) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : Dv,
                ((g⁻¹ : (Dv)ˣ) : Dv) * z * (g : Dv) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔ z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : Dv, z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v →
                ((g⁻¹ : (Dv)ˣ) : Dv) * z * (g : Dv) ∈ Submodule.localBox R v)) ∧
          (QuotientGroup.mk g : (Dv)ˣ ⧸ H) = c)} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      have hcl := clausesU_of_eq_mul_Dm' hϖ0 hϖO hϖu (isIntU_upper t.2) (by simpa using (isU_one : IsU (Ov) (1 : Kv)))
      rw [← hyRepk t, ← hgRep t] at hcl
      refine ⟨gRep t, ⟨?_, ?_, ?_⟩, rfl⟩
      · rw [hclause_i]; exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1⟩
      · rw [hclause_v]; exact hcl.2.2.2.2.1
      · rw [hclause_vi]; exact hcl.2.2.2.2.2
    · rintro c ⟨g, ⟨hi, hv, hvi⟩, rfl⟩
      rw [hclause_i] at hi
      rw [hclause_v] at hv
      rw [hclause_vi] at hvi
      obtain ⟨k, hk, hk11, hyk⟩ := normalFormU hϖ0 hϖO hmax hϖu _ (isUnit_det_psiP v φ hP g) hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hv hvi
      have ht : k 0 1 * (k 1 1)⁻¹ ∈ Ov := mul_mem (hk.1 0 1) hk11.inv.mem
      refine ⟨⟨_, ht⟩, ?_⟩
      show (gRep ⟨_, ht⟩ : (Dv)ˣ ⧸ H) = (g : (Dv)ˣ ⧸ H)
      rw [QuotientGroup.eq, hmemH, Units.val_mul, psiP_mul v φ hP, psiP_units_inv v φ hP, hgRep, hyk]
      exact isB_yRep_inv_mul hϖ0 hϖO hk hk11

  let I : Ideal (Ov) := Ideal.span {((q : ℕ) : Ov)}
  have hmemI : ∀ r : Ov, r ∈ I ↔ ((q : ℕ) : Kv)⁻¹ * (r : Kv) ∈ Ov := by
    intro r
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      have : ((q : ℕ) : Kv)⁻¹ * ((c * ((q : ℕ) : Ov) : Ov) : Kv) = c := by
        push_cast; rw [mul_comm (c : Kv), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
      rw [this]; exact c.2
    · intro hr
      refine ⟨⟨_, hr⟩, Subtype.ext ?_⟩
      push_cast; rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  have hrel : ∀ s t : Ov, I.quotientRel s t ↔ Setoid.ker F s t := by
    intro s t
    rw [Submodule.quotientRel_def, Setoid.ker_def, hker, hmemI]
    push_cast
    rw [show ((q : ℕ) : Kv)⁻¹ * ((s : Kv) - (t : Kv)) = -(((q : ℕ) : Kv)⁻¹ * ((t : Kv) - (s : Kv))) by ring]
    exact ⟨fun h => by simpa using neg_mem h, fun h => neg_mem h⟩
  have e : (Ov) ⧸ I ≃ Set.range F := (Quotient.congrRight hrel).trans (Setoid.quotientKerEquivRange F)
  have hcard : Nat.card ((Ov) ⧸ I) = q := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
      v q hq hqv q hq.ne_zero, Nat.Prime.factorization_self hq, pow_one]
  have hcount := e
  refine ⟨?_, fun g hg => ?_⟩
  · have h1 : Nat.card ↥(Set.range F) = q := by rw [← Nat.card_congr e, hcard]
    rw [hrange] at h1
    exact h1
  ·
    have h1 : Nat.card ↥(Set.range F) = q := by rw [← Nat.card_congr e, hcard]
    rw [hrange] at h1
    have hNF : ∀ x : (Dv)ˣ, NF v φ (P := P) q x ↔
        (((x : Dv) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ) • ((x⁻¹ : (Dv)ˣ) : Dv) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            ((x⁻¹ : (Dv)ˣ) : Dv) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
            (q : ℚ)⁻¹ • (x : Dv) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : Dv,
                ((x⁻¹ : (Dv)ˣ) : Dv) * z * (x : Dv) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔ z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
           ¬ (∀ z : Dv, z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v →
                ((x⁻¹ : (Dv)ˣ) : Dv) * z * (x : Dv) ∈ Submodule.localBox R v)) := by
      intro x
      constructor
      · rintro ⟨k, hk, hk11, hx⟩
        obtain ⟨c1, c2, c3, c4, c5, c6⟩ := clausesU_of_eq_mul_Dm' hϖ0 hϖO hϖu hk hk11
        rw [← hx] at c1 c2 c3 c4 c5 c6
        exact ⟨(hclause_i x).mpr ⟨c1, c2, c3, c4⟩, (hclause_v x).mpr c5, (hclause_vi x).mpr c6⟩
      · rintro ⟨hi, hv, hvi⟩
        obtain ⟨c1, c2, c3, c4⟩ := (hclause_i x).mp hi
        exact normalFormU hϖ0 hϖO hmax hϖu _ (isUnit_det_psiP v φ hP x) c1 c2 c3 c4 ((hclause_v x).mp hv) ((hclause_vi x).mp hvi)
    have hcountNF : Nat.card {c : (Dv)ˣ ⧸ H // ∃ x, NF v φ (P := P) q x ∧ (QuotientGroup.mk x : (Dv)ˣ ⧸ H) = c} = q :=
      (Nat.card_congr (Equiv.subtypeEquivRight fun c => by simp only [hNF, Set.mem_setOf_eq])).trans h1
    exact indicesU v φ hP q hϖ0 hϖO hϖu H hmemH hcountNF g ((hNF g).mpr hg)

end mainU

end F3LOC

open QuaternionAlgebra

theorem solution
    {a b : ℚ} (R Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} [NeZero N] (hN : Squarefree N)
    (hR : QuaternionAlgebra.IsEichlerOrder R N) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N) {q' : ℕ} [Fact q'.Prime] (hℓq' : q' ≠ ℓ)
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q') (hq'N : ¬ q' ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Nat.card {c : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) //
        ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
          (((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
            (ℓ : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
            ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
            (ℓ : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ↔ z ∈ Submodule.localBox R v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ Submodule.localBox R v →
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v)) ∧
          (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = c} = ℓ ∧
    ∀ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      (((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
            (ℓ : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
            ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
            (ℓ : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ↔ z ∈ Submodule.localBox R v) ∧
           ¬ (∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ Submodule.localBox R v →
                ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z * (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v)) →
        (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ⊓ (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).map (MulAut.conj g).toMonoidHom).relIndex (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = ℓ ∧
        (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ⊓ (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).map (MulAut.conj g⁻¹).toMonoidHom).relIndex (MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = ℓ := by
  classical

  have hab : a ≠ 0 ∧ b ≠ 0 := ⟨hdef.neg_left.ne, hdef.neg_right.ne⟩
  obtain ⟨Λ₂, hΛ₂, hR12, hidx⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree hdef hN Λ R hΛ hR hRΛ
  have hidx' : (Λ ⊓ Λ₂).toAddSubgroup.relIndex Λ.toAddSubgroup = N := by rw [← hR12]; exact hidx
  obtain ⟨m, hconj, hm₁, hmN⟩ :=
    QuaternionAlgebra.exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq q' hdef Λ Λ₂ hΛ hΛ₂ N hq'N hidx'
  have hRm : R = CerednikDrinfeld.meetOrder Λ m := by rw [hR12, ← hconj]; rfl
  subst hRm
  have hRN : (Λ ⊓ Submodule.conjByFiniteIdele Λ m).toAddSubgroup.relIndex Λ.toAddSubgroup = N := by rw [hconj]; exact hidx'
  obtain ⟨-, hloc⟩ := QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
    hab hΛ N m hm₁ hmN hRN
  obtain ⟨-, φ, hφ, hΛv, k₁, k₂, hk₁, hk₁i, hk₂, hk₂i, hmv⟩ := hloc v ℓ Fact.out hℓv hℓN

  have hval : padicValNat ℓ N = 1 := by
    have h1 : 1 ≤ padicValNat ℓ N := one_le_padicValNat_of_dvd (NeZero.ne N) hℓN
    have h2 : ¬ 2 ≤ padicValNat ℓ N := by
      intro h2
      have hdvd : ℓ ^ 2 ∣ N := (padicValNat_dvd_iff_le (NeZero.ne N)).mpr h2
      have hu := hN ℓ (by rw [← pow_two]; exact hdvd)
      rw [Nat.isUnit_iff] at hu
      exact (Fact.out : ℓ.Prime).one_lt.ne' hu
    omega
  rw [hval, pow_one] at hmv

  set P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v) := (k₁ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) with hPdef
  have hP : IsUnit P.det := Matrix.isUnits_det_units k₁
  have hk1U : F3LOC.IsIntU (HeightOneSpectrum.adicCompletionIntegers ℚ v) P :=
    ⟨hk₁, hP, by rw [hPdef, ← Matrix.coe_units_inv]; exact hk₁i⟩
  have hk2U : F3LOC.IsIntU (HeightOneSpectrum.adicCompletionIntegers ℚ v) (k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :=
    ⟨hk₂, Matrix.isUnits_det_units k₂, by rw [← Matrix.coe_units_inv]; exact hk₂i⟩
  have hRv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v, x ∈ Submodule.localBox Λ v ↔
      F3LOC.IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) (F3LOC.psiP v φ P x) := by
    intro x; rw [hΛv x]; unfold F3LOC.psiP; rw [hk1U.isInt_conj_iff]; rfl
  set mv : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ := Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m with hmvdef
  have hmv_val : (mv : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : _) := rfl
  have hmv_inv : ((mv⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : _) := by
    rw [hmvdef, Units.coe_map_inv]; rfl
  have hψm : F3LOC.psiP v φ P (mv : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) = F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) * ((k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * P) := by
    unfold F3LOC.psiP; rw [hmv_val, hmv, hPdef]; simp only [mul_assoc]
    rw [← mul_assoc (k₁ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))⁻¹, Matrix.nonsing_inv_mul _ hP, one_mul]; rfl
  have hR'v : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v, x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ m) v ↔
      F3LOC.IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        ((F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * F3LOC.psiP v φ P x * F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)) := by
    intro x
    rw [F3LOC.mem_localBox_conj_iff' v hΛ.isOrder m x, hRv, ← hmv_val, ← hmv_inv, F3LOC.psiP_mul v φ hP, F3LOC.psiP_mul v φ hP,
      F3LOC.psiP_units_inv v φ hP, hψm, Matrix.mul_inv_rev]
    have hkk : F3LOC.IsIntU (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * P) := hk2U.mul' hk1U
    rw [show ((k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * P)⁻¹ * (F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * F3LOC.psiP v φ P x *
          (F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) * ((k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * P))
        = ((k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * P)⁻¹ * ((F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * F3LOC.psiP v φ P x * F3LOC.Dm ((ℓ : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)) *
          ((k₂ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * P) by simp only [mul_assoc],
      hkk.isInt_conj_iff]

  exact F3LOC.mainU v φ hP hφ hΛ.isOrder m ℓ Fact.out hℓv hRv hR'v

end S_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree (solution)
