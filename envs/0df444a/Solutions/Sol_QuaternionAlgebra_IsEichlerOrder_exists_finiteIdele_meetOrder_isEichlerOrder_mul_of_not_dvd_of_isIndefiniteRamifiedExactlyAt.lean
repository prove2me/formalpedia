-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/47cc7bb2-81a1-5d76-8709-42417587696f

import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_units_localBox_atkinLehner_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "prime_iff cast_ne_zero coe_castRingHom cast_smul_eq_nsmul Coprime divisors Prime prime_iff_prime_int isCoprime_iff_coprime eq_zero_or_pos cast_zero castRingHom zero"
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

theorem disjoint_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ') :
    Disjoint (placesOf ℓ) (placesOf ℓ') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_placesOf_iff hℓ] at hv
  rw [mem_placesOf_iff hℓ'] at hv'
  have hcop : IsCoprime (ℓ : 𝓞 ℚ) (ℓ' : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (ℓ : ℤ) (ℓ' : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hv')

theorem not_mem_placesOf_of_mem_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ')
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ placesOf ℓ) : v ∉ placesOf ℓ' :=
  Finset.disjoint_left.mp (disjoint_placesOf_of_coprime hℓ hℓ' h) hv

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

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace HeckeLocal

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem box_eq_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure]; rfl

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, ?_⟩
  · have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
    rw [e]; exact one_mem _
  · rfl

theorem coe_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ u).mp hu

  have h1 : (u : ℍ𝔸) * 1 ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
    Set.smul_mem_smul_set (one_mem_box hΛ)
  rw [h, mul_one] at h1
  exact h1

theorem coe_inv_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  coe_mem_box_of_mem_stabilizer hΛ (inv_mem hu)

theorem mul_mem_primeHeckeSet_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    u * h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ hub h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact box_mul_mem hΛ h2 huib
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (((u * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (u : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem hub
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((ℓ : ℚ)⁻¹ • ((u * h : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [mul_smul_comm, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact box_mul_mem hΛ huib hmem

theorem mul_mem_primeHeckeSet_of_mem_stabilizer' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    h * u ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ h1 hub
  · rw [mul_inv_rev, Units.val_mul, ← mul_smul_comm]
    exact box_mul_mem hΛ huib h2
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (u : ℍ𝔸) * (((h * u)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact box_mul_mem hΛ hub hmem
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((ℓ : ℚ)⁻¹ • ((h * u : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [smul_mul_assoc, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem huib

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mem_stabilizer_of_coe_mem_of_coe_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) (hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact box_mul_mem hΛ hu hx
  · intro x hx
    refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
    show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem stabilizer_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (h : S ≤ R) : Submodule.finiteIdeleStabilizer S ≤ Submodule.finiteIdeleStabilizer R := by
  intro u hu
  exact mem_stabilizer_of_coe_mem_of_coe_inv_mem hR (box_mono h (coe_mem_box_of_mem_stabilizer hS hu))
    (box_mono h (coe_inv_mem_box_of_mem_stabilizer hS hu))

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

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
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c' * c, mul_mem hc' hc, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

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

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨z, hz, 1, one_mem _, rfl⟩

end HeckeLocal

set_option autoImplicit false

open scoped TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace AdelicSlice

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

def s1_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem s1_mem_Zhat_iff (a : 𝔸f) : a ∈ s1_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

theorem s1_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem s1_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, s1_valued_algebraMap_apply]

theorem s1_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem s1_valuation_natCast_le_one (v : HOS) (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  have h := s1_valuation_intCast_le_one v (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem s1_algebraMap_intCast_mem_Zhat (m : ℤ) : algebraMap ℚ 𝔸f (m : ℚ) ∈ s1_Zhat := fun v =>
  (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m)

theorem s1_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm

section BoxGen

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_tmul_mem_finiteAdeleBox {Λ : Submodule ℤ K} {z : K} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : a ∈ s1_Zhat) : z ⊗ₜ[ℚ] a ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem s1_finiteAdeleBox_le_iff {Λ : Submodule ℤ K} {H : AddSubgroup (K ⊗[ℚ] 𝔸f)} :
    Submodule.finiteAdeleBox Λ ≤ H ↔ ∀ z ∈ Λ, ∀ a : 𝔸f, a ∈ s1_Zhat → z ⊗ₜ[ℚ] a ∈ H := by
  unfold Submodule.finiteAdeleBox
  rw [AddSubgroup.closure_le]
  constructor
  · intro h z hz a ha
    exact h ⟨z, hz, a, ha, rfl⟩
  · rintro h x ⟨z, hz, a, ha, rfl⟩
    exact h z hz a ha

end BoxGen

section Slice

variable {K : Type*} [Ring K] [Algebra ℚ K]

def s1_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] 𝔸f →ₗ[ℚ] 𝔸f :=
  TensorProduct.lift ((LinearMap.lsmul ℚ 𝔸f).comp (b.coord i))

theorem s1_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (a : 𝔸f) :
    s1_coord b i (z ⊗ₜ[ℚ] a) = (b.repr z i) • a := by
  unfold s1_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem s1_coord_mem_Zhat_of_mem_finiteAdeleBox {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι)
    {t : K ⊗[ℚ] 𝔸f} (ht : t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))) :
    s1_coord b i t ∈ s1_Zhat := by
  have hle : Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ≤ (s1_Zhat.toAddSubgroup).comap (s1_coord b i).toAddMonoidHom := by
    rw [s1_finiteAdeleBox_le_iff]
    intro z hz a ha
    rw [AddSubgroup.mem_comap]
    show s1_coord b i (z ⊗ₜ[ℚ] a) ∈ s1_Zhat
    rw [s1_coord_tmul]
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
    rw [← hm, Algebra.smul_def]
    refine mul_mem ?_ ha
    have : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
    rw [this]
    exact s1_algebraMap_intCast_mem_Zhat m
  exact hle ht

theorem s1_tmul_one_mem_finiteAdeleBox_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (z : K) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ↔ z ∈ Submodule.span ℤ (Set.range b) := by
  constructor
  · intro hz
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b z]
    intro i
    have hc := s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i hz
    rw [s1_coord_tmul, Algebra.smul_def, mul_one] at hc
    have hval : ∀ v : HOS, v.valuation ℚ (b.repr z i) ≤ 1 := fun v =>
      (s1_algebraMap_apply_mem_integers_iff _ v).mp (hc v)
    obtain ⟨m, hm⟩ := s1_exists_intCast_of_forall_valuation_le_one _ hval
    refine ⟨m, ?_⟩
    rw [hm, algebraMap_int_eq, Int.coe_castRingHom]
  · intro hz
    exact s1_tmul_mem_finiteAdeleBox hz (one_mem _)

end Slice

end AdelicSlice

end

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace C8N

open Classical in
noncomputable scoped instance : DecidableEq (HeightOneSpectrum (𝓞 ℚ)) := Classical.decEq _

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "D_" v => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

structure LocalAL (R : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) (v : HeightOneSpectrum (𝓞 ℚ))
    (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : Prop where
  mem : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v
  qinv_mem : (q : ℚ) • (((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ∈ Submodule.localBox R v
  inv_notMem : ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v
  qinv_notMem : (q : ℚ)⁻¹ • (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v
  sq : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)

section idele

variable (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)

noncomputable def localData : ∀ v' : HeightOneSpectrum (𝓞 ℚ), (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ :=
  fun v' => if h : v' = v then h ▸ w else 1

theorem localData_self : localData v w v = w := by simp [localData]

theorem localData_ne {v' : HeightOneSpectrum (𝓞 ℚ)} (h : v' ≠ v) : localData v w v' = 1 := by simp [localData, h]

theorem exists_idele : ∃ n : (ℍ𝔸)ˣ, (ev v) (n : ℍ𝔸) = w ∧ ∀ v' ≠ v, (ev v') (n : ℍ𝔸) = 1 := by
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {v} (localData v w)
  refine ⟨β, ?_, fun v' hv' => ?_⟩
  · rw [h1 v (Finset.mem_singleton_self v), localData_self]
  · rw [h2 v' (by simpa using hv')]

end idele

theorem ev_inv (v' : HeightOneSpectrum (𝓞 ℚ)) (n : (ℍ𝔸)ˣ) :
    (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((Units.map (ev v').toRingHom.toMonoidHom n)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) :=
  (Units.coe_map_inv _ _).symm

theorem mem_primeHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (q : ℕ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) (hw : LocalAL R q v w)

    (hqv : ∀ v' : HeightOneSpectrum (𝓞 ℚ), v' ≠ v → algebraMap ℚ (v'.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ v'.adicCompletionIntegers ℚ)
    (n : (ℍ𝔸)ˣ) (hnv : (ev v) (n : ℍ𝔸) = w) (hnv' : ∀ v' ≠ v, (ev v') (n : ℍ𝔸) = 1) :
    n ∈ QuaternionAlgebra.primeHeckeSet R q := by
  have hbox := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox (D := ℍ[ℚ, a, b]) R hR.fg hR.spanTop x

  have hnu : ∀ v', Units.map (ev v').toRingHom.toMonoidHom n = (if h : v' = v then h ▸ w else 1 : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) := by
    intro v'
    ext
    by_cases h : v' = v
    · subst h; simp [hnv]
    · simp [hnv' v' h, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hbox]
    intro v'
    by_cases h : v' = v
    · subst h; rw [hnv]; exact hw.mem
    · rw [hnv' v' h]; exact HeckeLocal.one_mem_localBox hR v'
  ·
    rw [hbox]
    intro v'
    rw [map_smul, ev_inv, hnu]
    by_cases h : v' = v
    · subst h; simpa using hw.qinv_mem
    · simp only [h, ↓reduceDIte, inv_one, Units.val_one]
      rw [Nat.cast_smul_eq_nsmul]
      exact AddSubgroup.nsmul_mem _ (HeckeLocal.one_mem_localBox hR v') q
  ·
    intro hmem
    rw [hbox] at hmem
    have := hmem v
    rw [ev_inv, hnu] at this
    simp at this
    exact hw.inv_notMem this
  ·
    intro hmem
    rw [hbox] at hmem
    have := hmem v
    rw [map_smul, hnv] at this
    exact hw.qinv_notMem this

noncomputable def qDiag (q : ℕ) (hq : (q : ℚ) ≠ 0) : (ℍ𝔸)ˣ :=
  Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q : ℚ) hq))

noncomputable def qDiag' (q : ℕ) (hq : (q : ℚ) ≠ 0) : (ℍ𝔸)ˣ :=
  Units.map (algebraMap ℚ ℍ𝔸).toMonoidHom (Units.mk0 (q : ℚ) hq)

theorem val_qDiag (q : ℕ) (hq : (q : ℚ) ≠ 0) :
    ((qDiag (a := a) (b := b) q hq : (ℍ𝔸)ˣ) : ℍ𝔸) = algebraMap ℚ ℍ𝔸 (q : ℚ) := by
  rw [Algebra.TensorProduct.algebraMap_apply]; rfl

theorem qDiag_eq (q : ℕ) (hq : (q : ℚ) ≠ 0) : qDiag (a := a) (b := b) q hq = qDiag' q hq :=
  Units.ext (by rw [val_qDiag]; rfl)

theorem val_qDiag'_inv (q : ℕ) (hq : (q : ℚ) ≠ 0) :
    (((qDiag' (a := a) (b := b) q hq)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = algebraMap ℚ ℍ𝔸 ((q : ℚ)⁻¹) := by
  rw [qDiag', Units.coe_map_inv]
  simp

theorem isOrder_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n : (ℍ𝔸)ˣ) :
    QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) :=
  hR.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n)

theorem ev_u (q : ℕ) (hq0 : (q : ℚ) ≠ 0) (n : (ℍ𝔸)ˣ) (v' : HeightOneSpectrum (𝓞 ℚ)) :
    ((Units.map (ev v').toRingHom.toMonoidHom ((qDiag' q hq0)⁻¹ * (n * n)) : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)
      = algebraMap ℚ _ ((q : ℚ)⁻¹) * ((ev v') (n : ℍ𝔸) * (ev v') (n : ℍ𝔸)) := by
  rw [Units.coe_map, Units.val_mul, Units.val_mul, val_qDiag'_inv]
  simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe, map_mul, AlgHom.commutes]

theorem ev_u_inv (q : ℕ) (hq0 : (q : ℚ) ≠ 0) (n : (ℍ𝔸)ˣ) (v' : HeightOneSpectrum (𝓞 ℚ)) :
    ((((Units.map (ev v').toRingHom.toMonoidHom ((qDiag' q hq0)⁻¹ * (n * n)))⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ))
      = ((ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * algebraMap ℚ _ (q : ℚ) := by
  rw [← map_inv, mul_inv_rev, inv_inv, mul_inv_rev, Units.coe_map, Units.val_mul, Units.val_mul]
  simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe, map_mul, AlgHom.commutes,
    qDiag', Units.coe_map, Units.val_mk0]

theorem exists_sq {S : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (q : ℕ) (hq0 : (q : ℚ) ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hsq : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ))
    (hqv : ∀ v' : HeightOneSpectrum (𝓞 ℚ), v' ≠ v → algebraMap ℚ (v'.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ v'.adicCompletionIntegers ℚ)
    (n : (ℍ𝔸)ˣ) (hnv : (ev v) (n : ℍ𝔸) = w) (hnv' : ∀ v' ≠ v, (ev v') (n : ℍ𝔸) = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer S, n * n = qDiag q hq0 * u := by
  refine ⟨(qDiag' q hq0)⁻¹ * (n * n), ?_, by rw [qDiag_eq, mul_inv_cancel_left]⟩
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits S hS]
  intro v'
  rw [Submodule.mem_localBoxUnits_iff]
  have hwinv : ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) * ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) *
      algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ) = 1 := by
    rw [← hsq, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, show w⁻¹ * w⁻¹ * (w * w) = 1 by group, Units.val_one]
  have hU : ((Units.map (ev v').toRingHom.toMonoidHom ((qDiag' q hq0)⁻¹ * (n * n)) : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ) ∈ Submodule.localBox S v' := by
    rw [ev_u]
    by_cases h : v' = v
    · subst h
      rw [hnv, hsq, ← map_mul, inv_mul_cancel₀ hq0, map_one]
      exact HeckeLocal.one_mem_localBox hS _
    · rw [hnv' v' h, mul_one, mul_one, Algebra.TensorProduct.algebraMap_apply']
      simpa using HeckeLocal.tmul_one_mul_mem_localBox v' (hqv v' h) (HeckeLocal.one_mem_localBox hS v')
  have hUinv : ((((Units.map (ev v').toRingHom.toMonoidHom ((qDiag' q hq0)⁻¹ * (n * n)))⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)) ∈ Submodule.localBox S v' := by
    rw [ev_u_inv, ev_inv]
    by_cases h : v' = v
    · subst h

      have e : (Units.map (ev v').toRingHom.toMonoidHom n)⁻¹ = w⁻¹ := by
        rw [inv_inj]; ext; simpa using hnv
      rw [e, hwinv]
      exact HeckeLocal.one_mem_localBox hS _
    · have e : (Units.map (ev v').toRingHom.toMonoidHom n)⁻¹ = 1 := by
        have : Units.map (ev v').toRingHom.toMonoidHom n = 1 := by ext; simpa using hnv' v' h
        rw [this, inv_one]
      rw [e, Units.val_one, one_mul, one_mul, Algebra.TensorProduct.algebraMap_apply']
      refine HeckeLocal.mul_tmul_one_mem_localBox v' ?_ (HeckeLocal.one_mem_localBox hS v') |> fun h' => by simpa using h'
      simpa using (v'.adicCompletionIntegers ℚ).natCast_mem q
  exact ⟨hU, hUinv⟩

theorem tmul_one_mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (z : ℍ[ℚ, a, b]) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ↔ z ∈ Λ := by
  obtain ⟨B, -, hB⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hΛ
  rw [← hB]
  exact AdelicSlice.s1_tmul_one_mem_finiteAdeleBox_iff B z

theorem mem_conjByFiniteIdele_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Submodule.mem_conjByFiniteIdele_iff]
  constructor
  · rintro ⟨y, hy, hyz⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at hyz
    rw [← hyz, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

section norm

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (q : ℕ) (hq0 : (q : ℚ) ≠ 0)
  (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
  (hsq : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ))
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hnv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = w)
  (hnv' : ∀ v' ≠ v, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v' (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)

include hsq hq0 in

theorem val_winv : ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
    algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ((q : ℚ)⁻¹) * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
  have hq' : algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ((q : ℚ)⁻¹) * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = 1 := by
    rw [mul_assoc, hsq, ← map_mul, inv_mul_cancel₀ hq0, map_one]
  have e : ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      = (algebraMap ℚ _ ((q : ℚ)⁻¹) * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w) *
          ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
    rw [hq', one_mul]
  rw [e, mul_assoc, Units.mul_inv, mul_one]

include hsq hq0 in

theorem winv_mul_mul_w (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) * x * (w : _) =
      (w : _) * x * ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) := by
  rw [val_winv q hq0 v w hsq]
  rw [← mul_assoc ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x) _ _, ← Algebra.commutes ((q : ℚ)⁻¹) ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x)]
  simp only [mul_assoc]

include hR hnv hnv' hsq hq0 in

theorem conj_mem_localBox_meetOrder_iff (v' : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ) :
    (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (ev v') (n : ℍ𝔸) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v' ↔
      x ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v' := by
  have hRc := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  have hS : Submodule.localBox (CerednikDrinfeld.meetOrder R n) v' =
      Submodule.localBox R v' ⊓ Submodule.localBox (Submodule.conjByFiniteIdele R n) v' :=
    Submodule.localBox_inf R _ hR.fg hR.spanTop hRc.fg hRc.spanTop v'
  have hconj := fun y => Submodule.mem_localBox_conjByFiniteIdele_iff (D := ℍ[ℚ, a, b]) R hR.fg hR.spanTop n v' y
  by_cases h : v' = v
  · subst h

    have hninv : (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) : _) := by
      rw [ev_inv]; congr 1; rw [inv_inj]; ext; simpa using hnv
    rw [hninv, hnv, hS, AddSubgroup.mem_inf, AddSubgroup.mem_inf, hconj, hconj]
    simp only [hninv, hnv]
    have hxw : x = (w : _) * (((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) : _) * x * (w : _)) *
        ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ)ˣ) : _) := by
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    constructor
    · rintro ⟨h1, y, hy, hy'⟩
      refine ⟨?_, _, h1, hxw⟩

      have ex := hxw
      rw [hy', ← winv_mul_mul_w q hq0 v' w hsq, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
        Units.inv_mul, mul_one] at ex
      rw [ex]; exact hy
    · rintro ⟨h1, y, hy, hy'⟩
      refine ⟨?_, x, h1, by rw [winv_mul_mul_w q hq0 v' w hsq]⟩
      rw [hy', ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
      exact hy
  ·
    have h1' : (ev v') (n : ℍ𝔸) = 1 := hnv' v' h
    have h2' : (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by
      rw [ev_inv]; have : Units.map (ev v').toRingHom.toMonoidHom n = 1 := by ext; simpa using h1'
      rw [this, inv_one, Units.val_one]
    rw [h1', h2', one_mul, mul_one]

include hR hnv hnv' hsq hq0 in

theorem conjByFiniteIdele_meetOrder : Submodule.conjByFiniteIdele (CerednikDrinfeld.meetOrder R n) n = CerednikDrinfeld.meetOrder R n := by
  have hSo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) := isOrder_meetOrder hR n
  have hbox := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox (D := ℍ[ℚ, a, b]) _ hSo.fg hSo.spanTop x
  ext z
  rw [mem_conjByFiniteIdele_iff', ← tmul_one_mem_box_iff hSo z, hbox, hbox]
  refine forall_congr' fun v' => ?_
  rw [map_mul, map_mul]
  exact conj_mem_localBox_meetOrder_iff hR q hq0 v w hsq n hnv hnv' v' _

end norm

section sqprime

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (q : ℕ) (hq0 : (q : ℚ) ≠ 0)
  (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
  (hsq : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ))
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hnv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = w)
  (hnv' : ∀ v' ≠ v, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v' (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)

include hR hq0 hsq hnv hnv' in

theorem conj_mem_stabilizer_meetOrder {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) :
    n⁻¹ * u * n ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n) := by
  have hSo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) := isOrder_meetOrder hR n
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hSo] at hu ⊢
  intro v'
  have h := hu v'
  rw [Submodule.mem_localBoxUnits_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe] at h1 ⊢
    rw [Units.coe_map, Units.val_mul, Units.val_mul]
    simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe, map_mul]
    rw [conj_mem_localBox_meetOrder_iff hR q hq0 v w hsq n hnv hnv']
    simpa using h1
  · rw [SetLike.mem_coe] at h2 ⊢
    rw [← map_inv, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.coe_map, Units.val_mul, Units.val_mul]
    simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe, map_mul]
    rw [conj_mem_localBox_meetOrder_iff hR q hq0 v w hsq n hnv hnv']
    simpa [← map_inv] using h2

theorem classSetShift_classSetShift_eq_self_of
    (U : Subgroup (ℍ𝔸)ˣ) (m : (ℍ𝔸)ˣ) (hnorm : ∀ u ∈ U, m⁻¹ * u * m ∈ U)
    (c : ℚ) (hc : c ≠ 0) (u₀ : (ℍ𝔸)ˣ) (hu₀ : u₀ ∈ U)
    (hmm : m * m = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 c hc)) * u₀)
    (x : QuaternionAlgebra.ClassSet U) :
    CerednikDrinfeld.classSetShift U m (CerednikDrinfeld.classSetShift U m x) = x := by
  classical
  set δc : (ℍ𝔸)ˣ :=
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 c hc)) with hδc
  have hcentral : ∀ y : (ℍ𝔸)ˣ, δc * y = y * δc := by
    intro y
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hδc, Submodule.val_finiteIdeleDiagonal_apply]
    show (algebraMap ℚ ℍ[ℚ, a, b] c) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * (y : ℍ𝔸) = (y : ℍ𝔸) * ((algebraMap ℚ ℍ[ℚ, a, b] c) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
    have : (algebraMap ℚ ℍ[ℚ, a, b] c) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ ℍ𝔸 c := rfl
    rw [this]
    exact Algebra.commutes c _
  unfold CerednikDrinfeld.classSetShift
  set y := x.out * m with hy
  have hmid : QuaternionAlgebra.ClassSet.mk U ((QuaternionAlgebra.ClassSet.mk U y).out * m) =
      QuaternionAlgebra.ClassSet.mk U (y * m) := by
    have hrel : QuaternionAlgebra.ClassSet.mk U (QuaternionAlgebra.ClassSet.mk U y).out = QuaternionAlgebra.ClassSet.mk U y :=
      Quotient.out_eq _
    obtain ⟨δ, hδ, w', hw', hout⟩ := (DoubleCoset.eq _ _ _ _).mp hrel.symm
    rw [hout, mul_assoc (δ * y), show δ * y * (w' * m) = δ * (y * m * (m⁻¹ * w' * m)) by group]
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hδ
    rw [QuaternionAlgebra.ClassSet.mk_diagonal_mul, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ (hnorm w' hw')]
  rw [hmid, hy, mul_assoc, hmm, ← mul_assoc, ← hcentral, mul_assoc]
  rw [show δc * (x.out * u₀) = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 c hc)) * (x.out * u₀) from rfl,
    QuaternionAlgebra.ClassSet.mk_diagonal_mul, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ hu₀]
  exact Quotient.out_eq _

include hR hq0 hsq hnv hnv' in

theorem classSetShift_involutive (u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
    (hnn : n * n = qDiag q hq0 * u)
    (x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))) :
    CerednikDrinfeld.classSetShift _ n (CerednikDrinfeld.classSetShift _ n x) = x :=
  classSetShift_classSetShift_eq_self_of _ n (fun u' hu' => conj_mem_stabilizer_meetOrder hR q hq0 v w hsq n hnv hnv' hu')
    (q : ℚ) hq0 u hu hnn x

end sqprime

section eichler

variable {R Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
  (hR12 : R = Λ₁ ⊓ Λ₂) {N : ℕ} (hidx : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
  (q : ℕ) (hq0 : (q : ℚ) ≠ 0)
  (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
  (hsq : (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ))

  (hmax₁ : Submodule.localBox Λ₁ v = Submodule.localBox R v) (hmax₂ : Submodule.localBox Λ₂ v = Submodule.localBox R v)

  (hdidx : ∀ O' : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
      (∀ x, x ∈ O' ↔ ((w⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) * x * (w : _) ∈ Submodule.localBox R v) →
      (Submodule.localBox R v ⊓ O').relIndex (Submodule.localBox R v) = q)
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hnv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = w)
  (hnv' : ∀ v' ≠ v, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v' (n : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)

theorem mem_localBox_conj_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (g : (ℍ𝔸)ˣ)
    (v' : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v'.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ g) v' ↔
      (ev v') ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (ev v') (g : ℍ𝔸) ∈ Submodule.localBox Λ v' := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff (D := ℍ[ℚ, a, b]) Λ hΛ.fg hΛ.spanTop g v' x]
  have hgi : (ev v') ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (ev v') (g : ℍ𝔸) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hgi' : (ev v') (g : ℍ𝔸) * (ev v') ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← mul_assoc, ← mul_assoc, hgi, one_mul, mul_assoc, hgi, mul_one]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, ← mul_assoc, hgi', one_mul, mul_assoc, hgi', mul_one]

include hΛ₁ hΛ₂ hR12 in
theorem isOrder_R : QuaternionAlgebra.IsOrder R := by rw [hR12]; exact hΛ₁.isOrder.inf hΛ₂.isOrder

include hΛ₁ hΛ₂ hR12 hq0 hsq hmax₁ hmax₂ hnv hnv' in

theorem meetOrder_eq_inf_conj : CerednikDrinfeld.meetOrder R n = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₂ n := by
  have hRo : QuaternionAlgebra.IsOrder R := isOrder_R hΛ₁ hΛ₂ hR12
  have hSo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) := isOrder_meetOrder hRo n
  have hRc := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n
  have hΛ₂c := QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₂ hΛ₂.isOrder n
  have hTo : QuaternionAlgebra.IsOrder (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₂ n) := hΛ₁.isOrder.inf hΛ₂c
  have hboxS := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox (D := ℍ[ℚ, a, b]) _ hSo.fg hSo.spanTop x
  have hboxT := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox (D := ℍ[ℚ, a, b]) _ hTo.fg hTo.spanTop x

  have hS := fun v' => Submodule.localBox_inf R _ hRo.fg hRo.spanTop hRc.fg hRc.spanTop v'
  have hT := fun v' => Submodule.localBox_inf Λ₁ _ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop hΛ₂c.fg hΛ₂c.spanTop v'
  have hRl : ∀ v', Submodule.localBox R v' = Submodule.localBox Λ₁ v' ⊓ Submodule.localBox Λ₂ v' := fun v' => by
    conv_lhs => rw [hR12]
    exact Submodule.localBox_inf Λ₁ Λ₂ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop hΛ₂.isOrder.fg hΛ₂.isOrder.spanTop v'
  ext z
  rw [← tmul_one_mem_box_iff hSo, ← tmul_one_mem_box_iff hTo, hboxS, hboxT]
  refine forall_congr' fun v' => ?_

  generalize (ev v') (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = x
  show x ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v' ↔ x ∈ Submodule.localBox (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₂ n) v'
  rw [show CerednikDrinfeld.meetOrder R n = R ⊓ Submodule.conjByFiniteIdele R n from rfl, hS, hT, AddSubgroup.mem_inf, AddSubgroup.mem_inf,
    mem_localBox_conj_iff hRo, mem_localBox_conj_iff hΛ₂.isOrder]
  by_cases h : v' = v
  · subst h

    rw [hmax₁, hmax₂]
  ·
    have h1 : (ev v') (n : ℍ𝔸) = 1 := hnv' v' h
    have h2 : (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by
      rw [ev_inv]; have : Units.map (ev v').toRingHom.toMonoidHom n = 1 := by ext; simpa using h1
      rw [this, inv_one, Units.val_one]
    rw [h1, h2, one_mul, mul_one, hRl, AddSubgroup.mem_inf]
    tauto

include hΛ₁ hΛ₂ hR12 hidx hdidx hnv hnv' in

theorem relIndex_meetOrder : (CerednikDrinfeld.meetOrder R n).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N * q := by
  have hRo : QuaternionAlgebra.IsOrder R := isOrder_R hΛ₁ hΛ₂ hR12
  have hSo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) := isOrder_meetOrder hRo n
  have hRc := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n
  have hSR : CerednikDrinfeld.meetOrder R n ≤ R := inf_le_left
  have hRΛ : R ≤ Λ₁ := by rw [hR12]; exact inf_le_left

  rw [← AddSubgroup.relIndex_mul_relIndex (CerednikDrinfeld.meetOrder R n).toAddSubgroup R.toAddSubgroup Λ₁.toAddSubgroup
    (Submodule.toAddSubgroup_mono hSR) (Submodule.toAddSubgroup_mono hRΛ), hidx, mul_comm]
  congr 1

  rw [Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox R (CerednikDrinfeld.meetOrder R n) hRo.fg hRo.spanTop hSo.fg hSo.spanTop hSR]
  rw [finprod_eq_single _ v]
  ·
    rw [show CerednikDrinfeld.meetOrder R n = R ⊓ Submodule.conjByFiniteIdele R n from rfl,
      Submodule.localBox_inf R _ hRo.fg hRo.spanTop hRc.fg hRc.spanTop v]
    refine hdidx _ fun x => ?_
    rw [mem_localBox_conj_iff hRo, ev_inv, hnv]
    have e : (Units.map (ev v).toRingHom.toMonoidHom n)⁻¹ = w⁻¹ := by rw [inv_inj]; ext; simpa using hnv
    rw [e]
  · intro v' hv'

    have h1 : (ev v') (n : ℍ𝔸) = 1 := hnv' v' hv'
    have h2 : (ev v') ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by
      rw [ev_inv]; have : Units.map (ev v').toRingHom.toMonoidHom n = 1 := by ext; simpa using h1
      rw [this, inv_one, Units.val_one]
    have : Submodule.localBox (CerednikDrinfeld.meetOrder R n) v' = Submodule.localBox R v' := by
      rw [show CerednikDrinfeld.meetOrder R n = R ⊓ Submodule.conjByFiniteIdele R n from rfl,
        Submodule.localBox_inf R _ hRo.fg hRo.spanTop hRc.fg hRc.spanTop v']
      refine le_antisymm inf_le_left (le_inf le_rfl fun x hx => ?_)
      rw [mem_localBox_conj_iff hRo, h1, h2, one_mul, mul_one]; exact hx
    rw [this, AddSubgroup.relIndex_self]

include hΛ₁ hΛ₂ hR12 hidx hq0 hsq hmax₁ hmax₂ hdidx hnv hnv' in

theorem isEichlerOrder_meetOrder : QuaternionAlgebra.IsEichlerOrder (CerednikDrinfeld.meetOrder R n) (N * q) :=
  ⟨Λ₁, Submodule.conjByFiniteIdele Λ₂ n, hΛ₁, QuaternionAlgebra.IsMaximalOrder.conjByFiniteIdele hΛ₂ n,
    meetOrder_eq_inf_conj hΛ₁ hΛ₂ hR12 q hq0 v w hsq hmax₁ hmax₂ n hnv hnv',
    relIndex_meetOrder hΛ₁ hΛ₂ hR12 hidx q v w hdidx n hnv hnv'⟩

end eichler

noncomputable def placeOfPrime (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span {(q : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩

theorem natCast_mem_placeOfPrime (q : ℕ) (hq : q.Prime) : ((q : ℕ) : 𝓞 ℚ) ∈ (placeOfPrime q hq).asIdeal :=
  Ideal.subset_span (Set.mem_singleton _)

end C8N
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt.C8N"

open C8N in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N) :
    ∃ n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      QuaternionAlgebra.IsEichlerOrder (CerednikDrinfeld.meetOrder R n) (N * ℓ) := by
  have hq0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero

  set v := placeOfPrime ℓ hℓ with hv
  have hqv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := natCast_mem_placeOfPrime ℓ hℓ
  obtain ⟨w, ⟨ha1, -, ha3, -⟩, ⟨hs1, hs2⟩, hb, hd⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_units_localBox_atkinLehner_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
      hB hR ℓ hℓ hℓq hℓq' hℓN v hqv

  obtain ⟨n, hnv, hnv'⟩ := exists_idele v w

  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, hR12, hidx⟩ := hR
  have hRE : QuaternionAlgebra.IsEichlerOrder R N := ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, hR12, hidx⟩
  have hle₁ : R ≤ Λ₁ := by rw [hR12]; exact inf_le_left
  have hle₂ : R ≤ Λ₂ := by rw [hR12]; exact inf_le_right
  have hmax₁ := QuaternionAlgebra.IsEichlerOrder.localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
    hB hRE ℓ hℓ hℓq hℓq' hℓN v hqv hΛ₁ hle₁
  have hmax₂ := QuaternionAlgebra.IsEichlerOrder.localBox_eq_localBox_of_isMaximalOrder_of_le_of_isIndefiniteRamifiedExactlyAt_of_not_dvd
    hB hRE ℓ hℓ hℓq hℓq' hℓN v hqv hΛ₂ hle₂
  exact ⟨n, isEichlerOrder_meetOrder hΛ₁ hΛ₂ hR12 hidx ℓ hq0 v w hb hmax₁ hmax₂ hd n hnv hnv'⟩

end S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt (solution)
