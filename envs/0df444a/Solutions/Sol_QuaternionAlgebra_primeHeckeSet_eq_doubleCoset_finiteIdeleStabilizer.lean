-- Prove2me | solution 1 for QuaternionAlgebra.primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b863ff91-0f21-5dd3-9a92-a395dae985ca

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_eq_eq_succ
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "prime_iff card_coe_set_eq card_eq_fintype_card mod_eq_of_lt count prime_dvd_prime_iff_eq cast_smul_eq_nsmul Coprime divisors Prime prime_iff_prime_int isValue isCoprime_iff_coprime eq_zero_or_pos card_fin cast_zero castRingHom card_congr all zero mul_eq_zero"
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

private theorem _root_.HeckeLocal.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

p2m_export "HeckeLocal" "mem_stabilizer_iff"

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

namespace C4T

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open HeckeLocal

theorem mul_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {u u' : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) (hu' : u' ∈ Submodule.localBoxUnits Λ w) :
    u * u' ∈ Submodule.localBoxUnits Λ w := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact localBox_mul_mem hΛ w hu.1 hu'.1
  · rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hu'.2 hu.2

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ))
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) : u⁻¹ ∈ Submodule.localBoxUnits Λ w :=
  ⟨hu.2, by rw [inv_inv]; exact hu.1⟩

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ w :=
  ⟨by rw [Units.val_one]; exact one_mem_localBox hΛ w, by rw [inv_one, Units.val_one]; exact one_mem_localBox hΛ w⟩

theorem mem_stabilizer_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
    g ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) ↔
      g ∈ Submodule.localBoxUnits Λ w := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := inv_mem hg
    rw [MulAction.mem_stabilizer_iff] at hg hg'
    refine ⟨?_, ?_⟩
    · have h1 : (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg, mul_one] at h1; exact h1
    · have h1 : ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g⁻¹ • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg', mul_one] at h1; exact h1
  · rintro ⟨h1, h2⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact localBox_mul_mem hΛ w h1 hx
    · intro x hx
      refine ⟨(g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) • x, localBox_mul_mem hΛ w h2 hx, ?_⟩
      show (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

theorem finiteAdeleEvalAt_smul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (c • x) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x := by
  rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def]
  try rfl

theorem natCast_smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℕ)
    {y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) : (q : ℚ) • y ∈ Submodule.localBox Λ w := by
  rw [Nat.cast_smul_eq_nsmul ℚ]; exact AddSubgroup.nsmul_mem _ hy q

theorem inv_natCast_integral_of_ne {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : w ≠ v) :
    algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  apply Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq.ne_zero
  intro hmem
  rw [Nat.mem_placesOf_iff hq.ne_zero] at hmem
  exact hw (Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hmem hqv)

theorem exists_natCast_mem_asIdeal {q : ℕ} (hq : q.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  ⟨⟨Ideal.span {(q : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩,
    Ideal.mem_span_singleton_self _⟩

def OffUnit (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (h : (ℍ𝔸)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ w

theorem offUnit_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ q) : OffUnit Λ v h :=
  fun w hw => map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet q hh w (inv_natCast_integral_of_ne hq hqv hw)

theorem exists_offUnit_map_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ∃ β : (ℍ𝔸)ˣ, Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β = g ∧ OffUnit Λ v β := by
  classical
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {v}
    (Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) v g)
  have h1v := h1 v (Finset.mem_singleton_self v)
  rw [Function.update_self] at h1v
  refine ⟨β, Units.ext h1v, fun w hw => ?_⟩
  have e : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom β = 1 := Units.ext (h2 w (fun hmem => hw (Finset.mem_singleton.mp hmem)))
  rw [e]; exact one_mem_localBoxUnits hΛ w

theorem mem_box_iff_local {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox X w) :
    x ∈ Submodule.finiteAdeleBox X ↔ Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox X v := by
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · exact hx w hw

def locT (R : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {g |
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v)}

theorem mem_primeHeckeSet_iff_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {h : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) :
    h ∈ QuaternionAlgebra.primeHeckeSet R q ↔ Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ locT R q v := by
  have off1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (h : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).1
  have off2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).2
  have off3 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by rw [map_smul]; exact natCast_smul_mem_localBox w q (off2 w hw)
  have off4 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ)⁻¹ • (h : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by
      rw [finiteAdeleEvalAt_smul]
      exact tmul_one_mul_mem_localBox w (inv_natCast_integral_of_ne hq hqv hw) (off1 w hw)
  rw [QuaternionAlgebra.mem_primeHeckeSet_iff, mem_box_iff_local hRo v off1, mem_box_iff_local hRo v off3,
    mem_box_iff_local hRo v off2, mem_box_iff_local hRo v off4, map_smul, map_smul]
  exact Iff.rfl

theorem map_mem_stabilizer_of_mem_finiteIdeleStabilizer {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo] at hu
  exact (mem_stabilizer_localBox_iff hRo v _).mpr (hu v)

theorem inv_mul_mem_finiteIdeleStabilizer_of_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    {v : HeightOneSpectrum (𝓞 ℚ)} {h h' : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) (hoff' : OffUnit R v h')
    (hK : (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ * Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h' ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) :
    h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo]
  intro w
  rw [map_mul, map_inv]
  by_cases hw : w = v
  · subst hw; exact (mem_stabilizer_localBox_iff hRo _ _).mp hK
  · exact mul_mem_localBoxUnits hRo w (inv_mem_localBoxUnits w (hoff w hw)) (hoff' w hw)

theorem ncard_eq_ncard_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Set.ncard (QuotientGroup.mk '' QuaternionAlgebra.primeHeckeSet R q :
        Set ((ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R)) =
      Set.ncard (QuotientGroup.mk '' locT R q v : Set ((ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)))) := by
  set U := Submodule.finiteIdeleStabilizer R with hU
  set K := MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) with hK
  set T := QuaternionAlgebra.primeHeckeSet R q with hT
  set f : (ℍ𝔸)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ := Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom with hf
  have hfU : ∀ x y : (ℍ𝔸)ˣ, x⁻¹ * y ∈ U → (f x)⁻¹ * f y ∈ K := fun x y hxy => by
    rw [← map_inv, ← map_mul]; exact map_mem_stabilizer_of_mem_finiteIdeleStabilizer hRo v hxy
  let φ : (ℍ𝔸)ˣ ⧸ U → (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ K :=
    Quotient.map' f (fun x y hxy => QuotientGroup.leftRel_apply.mpr (hfU x y (QuotientGroup.leftRel_apply.mp hxy)))
  have hφ : ∀ h : (ℍ𝔸)ˣ, φ (h : (ℍ𝔸)ˣ ⧸ U) = ((f h : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ K) := fun h => rfl
  have hoffT : ∀ h ∈ T, OffUnit R v h := fun h hh => offUnit_of_mem_primeHeckeSet hq hqv hh
  have hfT : f '' T = locT R q v := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (mem_primeHeckeSet_iff_local hRo hq hqv (hoffT h hh)).mp hh
    · intro hg
      obtain ⟨β, hβ, hoff⟩ := exists_offUnit_map_eq hRo v g
      refine ⟨β, (mem_primeHeckeSet_iff_local hRo hq hqv hoff).mpr ?_, hβ⟩
      rw [hβ]; exact hg
  have hinj : Set.InjOn φ (QuotientGroup.mk '' T) := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨h', hh', rfl⟩ heq
    rw [hφ, hφ, QuotientGroup.eq] at heq
    rw [QuotientGroup.eq]
    exact inv_mul_mem_finiteIdeleStabilizer_of_local hRo (hoffT h hh) (hoffT h' hh') heq
  have hcomp : φ '' (QuotientGroup.mk '' T) = QuotientGroup.mk '' (f '' T) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr' fun h => hφ h
  rw [← hinj.ncard_image, hcomp, hfT]

theorem natCard_eq_natCard_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Nat.card {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R //
      ∃ g ∈ QuaternionAlgebra.primeHeckeSet R q,
        (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c} =
    Nat.card {c : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
        MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) //
      ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
        (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
          MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = c} := by
  have e1 := Nat.card_coe_set_eq (QuotientGroup.mk '' QuaternionAlgebra.primeHeckeSet R q :
        Set ((ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R))
  have e2 := Nat.card_coe_set_eq (QuotientGroup.mk '' locT R q v : Set ((ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))))
  have h2 : (QuotientGroup.mk '' locT R q v : Set ((ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)))) =
      {c | ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
        (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
          MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = c} := by
    ext c
    simp only [locT, Set.mem_setOf_eq, Set.mem_image, and_assoc]
  rw [h2] at e2
  exact e1.symm.trans ((ncard_eq_ncard_local hRo hq hqv).trans e2)

end C4T

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace TqLoc

section Places

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem eq_place_of_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = 𝔳 := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  apply Subtype.ext
  change Rat.HeightOneSpectrum.natGenerator w = q
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).1
    ((natCast_mem_asIdeal_iff w q).1 hw)

theorem natCast_mem_asIdeal_place_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ (𝔳).asIdeal ↔ q ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem asIdeal_place_eq_span : (𝔳).asIdeal = Ideal.span {(q : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) 𝔳
  rw [natGenerator_place] at h
  have h2 : (𝔳).asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) (𝔳).asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_q : (𝔳).valuation ℚ (q : ℚ) = WithZero.exp (-1) := by
  rw [show (q : ℚ) = algebraMap (𝓞 ℚ) ℚ q from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast hq.ne_zero) (asIdeal_place_eq_span q hq)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem valued_q : Valued.v ((q : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_q]

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem q_mem_integers : ((q : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers _ q

theorem q_inv_notMem_integers : ((q : ℕ) : 𝕂)⁻¹ ∉ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_q, ← WithZero.exp_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  norm_num

def toPadicInt [Fact q.Prime] : 𝓞v ≃A[ℤ] ℤ_[q] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, hq⟩).symm

def residue : 𝓞v →+* ZMod q :=
  haveI : Fact q.Prime := ⟨hq⟩
  (PadicInt.toZMod (p := q)).comp (toPadicInt q hq).toRingEquiv.toRingHom

theorem residue_natCast (n : ℕ) : residue q hq (n : 𝓞v) = n := by
  haveI : Fact q.Prime := ⟨hq⟩
  simp [residue]

theorem residue_eq_zero_iff (c : 𝓞v) :
    residue q hq c = 0 ↔ ∃ y : 𝓞v, c = ((q : ℕ) : 𝓞v) * y := by
  haveI : Fact q.Prime := ⟨hq⟩
  set e := toPadicInt q hq
  change PadicInt.toZMod (e c) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, e.injective ?_⟩
    change e c = e _
    rw [map_mul, map_natCast, ContinuousAlgEquiv.apply_symm_apply, mul_comm, hz]
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    change _ = e _
    rw [map_mul, map_natCast, mul_comm]

theorem q_inv_mul_mem_integers_iff (c : 𝕂) (hc : c ∈ 𝓞v) :
    ((q : ℕ) : 𝕂)⁻¹ * c ∈ 𝓞v ↔ residue q hq ⟨c, hc⟩ = 0 := by
  rw [residue_eq_zero_iff]
  constructor
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    change c = (q : 𝕂) * (((q : ℕ) : 𝕂)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ (q_ne_zero' q hq), one_mul]
  · rintro ⟨y, hy⟩
    have : c = ((q : ℕ) : 𝕂) * (y : 𝕂) := by
      have := congrArg Subtype.val hy; simpa using this
    rw [this, ← mul_assoc, inv_mul_cancel₀ (q_ne_zero' q hq), one_mul]
    exact y.2

open Classical in

def red (c : 𝕂) : ZMod q := if hc : c ∈ 𝓞v then residue q hq ⟨c, hc⟩ else 0

theorem red_of_mem {c : 𝕂} (hc : c ∈ 𝓞v) : red q hq c = residue q hq ⟨c, hc⟩ := by
  rw [red, dif_pos hc]

theorem red_add {c d : 𝕂} (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) : red q hq (c + d) = red q hq c + red q hq d := by
  rw [red_of_mem q hq hc, red_of_mem q hq hd, red_of_mem q hq (add_mem hc hd), ← map_add]; rfl

theorem red_mul {c d : 𝕂} (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) : red q hq (c * d) = red q hq c * red q hq d := by
  rw [red_of_mem q hq hc, red_of_mem q hq hd, red_of_mem q hq (mul_mem hc hd), ← map_mul]; rfl

theorem red_neg {c : 𝕂} (hc : c ∈ 𝓞v) : red q hq (-c) = -red q hq c := by
  rw [red_of_mem q hq hc, red_of_mem q hq (neg_mem hc), ← map_neg]; rfl

theorem red_sub {c d : 𝕂} (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) : red q hq (c - d) = red q hq c - red q hq d := by
  rw [sub_eq_add_neg, red_add q hq hc (neg_mem hd), red_neg q hq hd, sub_eq_add_neg]

theorem red_natCast (n : ℕ) : red q hq ((n : ℕ) : 𝕂) = n := by
  rw [red_of_mem q hq (natCast_mem_integers _ n)]
  exact residue_natCast q hq n

theorem red_q : red q hq ((q : ℕ) : 𝕂) = 0 := by
  rw [red_natCast, ZMod.natCast_self]

theorem q_inv_mul_mem_iff_red {c : 𝕂} (hc : c ∈ 𝓞v) : ((q : ℕ) : 𝕂)⁻¹ * c ∈ 𝓞v ↔ red q hq c = 0 := by
  rw [red_of_mem q hq hc]; exact q_inv_mul_mem_integers_iff q hq c hc

theorem red_natCast_val (t : ZMod q) : haveI : NeZero q := ⟨hq.ne_zero⟩; red q hq ((t.val : ℕ) : 𝕂) = t := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [red_natCast, ZMod.natCast_zmod_val]

end Places

section Local

variable (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (M : M₂) : M ∈ intMat q hq ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

def rep : Option (Fin q) → M₂
  | some t => !![1, 0; ((t : ℕ) : 𝕂), ϖ]
  | none => !![ϖ, 0; 0, 1]

def repInv : Option (Fin q) → M₂
  | some t => !![1, 0; -(ϖ⁻¹ * ((t : ℕ) : 𝕂)), ϖ⁻¹]
  | none => !![ϖ⁻¹, 0; 0, 1]

theorem rep_mul_repInv (o : Option (Fin q)) : rep q hq o * repInv q hq o = 1 := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hq0]
  | some t =>
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hq0]
    ring_nf
    rw [mul_inv_cancel_right₀ hq0, sub_self]

theorem repInv_mul_rep (o : Option (Fin q)) : repInv q hq o * rep q hq o = 1 := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hq0]
  | some t =>
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hq0]

theorem rep_mem_intMat (o : Option (Fin q)) : rep q hq o ∈ intMat q hq := by
  cases o with
  | none => intro i j; fin_cases i <;> fin_cases j <;> simp [rep, one_mem, zero_mem, q_mem_integers q hq]
  | some t =>
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [rep, one_mem, zero_mem, q_mem_integers q hq, natCast_mem_integers]

theorem smul_repInv_mem_intMat (o : Option (Fin q)) : ϖ • repInv q hq o ∈ intMat q hq := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [repInv, one_mem, zero_mem, q_mem_integers q hq, mul_inv_cancel₀ hq0]
  | some t =>
    intro i j; fin_cases i <;> fin_cases j
    · simp [repInv, q_mem_integers q hq]
    · simp [repInv, zero_mem]
    · simp only [repInv, Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.mk_one, Fin.zero_eta, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
      exact neg_mem (natCast_mem_integers _ _)
    · simp [repInv, mul_inv_cancel₀ hq0, one_mem]

theorem repInv_notMem_intMat (o : Option (Fin q)) : repInv q hq o ∉ intMat q hq := by
  intro h
  cases o with
  | none => have := h 0 0; simp [repInv] at this; exact q_inv_notMem_integers q hq this
  | some t => have := h 1 1; simp [repInv] at this; exact q_inv_notMem_integers q hq this

theorem smul_rep_notMem_intMat (o : Option (Fin q)) : ϖ⁻¹ • rep q hq o ∉ intMat q hq := by
  have hq0 := q_ne_zero' q hq
  intro h
  cases o with
  | none => have := h 1 1; simp [rep] at this; exact q_inv_notMem_integers q hq this
  | some t => have := h 0 0; simp [rep] at this; exact q_inv_notMem_integers q hq this

theorem eq_of_repInv_mul_rep_mem (o o' : Option (Fin q)) (h : repInv q hq o * rep q hq o' ∈ intMat q hq) :
    o = o' := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some t' =>
      exfalso
      have := h 0 0
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact q_inv_notMem_integers q hq this
  | some t =>
    cases o' with
    | none =>
      exfalso
      have := h 1 1
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact q_inv_notMem_integers q hq this
    | some t' =>
      congr 1
      have h10 := h 1 0
      simp only [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two] at h10
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
        Fin.mk_one, Fin.zero_eta] at h10

      have hmem : ((q : ℕ) : 𝕂)⁻¹ * (((t' : ℕ) : 𝕂) - ((t : ℕ) : 𝕂)) ∈ 𝓞v := by
        have : ((q : ℕ) : 𝕂)⁻¹ * (((t' : ℕ) : 𝕂) - ((t : ℕ) : 𝕂)) =
            -(((q : ℕ) : 𝕂)⁻¹ * ((t : ℕ) : 𝕂)) * 1 + ((q : ℕ) : 𝕂)⁻¹ * ((t' : ℕ) : 𝕂) := by ring
        rw [this]; exact h10
      rw [q_inv_mul_mem_iff_red q hq (sub_mem (natCast_mem_integers _ _) (natCast_mem_integers _ _)),
        red_sub q hq (natCast_mem_integers _ _) (natCast_mem_integers _ _), red_natCast, red_natCast,
        sub_eq_zero] at hmem

      apply Fin.ext
      have h1 := congrArg ZMod.val hmem
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt t'.2, Nat.mod_eq_of_lt t.2, eq_comm] at h1

theorem field_dichotomy {F : Type*} [Field F] (x y : Fin 2 → Fin 2 → F)
    (hE : ∀ i j, x i 0 * y 0 j + x i 1 * y 1 j = 0) (hF : ∀ i j, y i 0 * x 0 j + y i 1 * x 1 j = 0)
    (hy : ∃ i j, y i j ≠ 0) (hx : ∃ i j, x i j ≠ 0) :
    (∃ t : F, (∀ j, x 1 j = t * x 0 j) ∧ ∀ i, y i 0 + t * y i 1 = 0) ∨
    ((∀ j, x 0 j = 0) ∧ ∀ i, y i 1 = 0) := by
  by_cases hrow : x 0 0 = 0 ∧ x 0 1 = 0
  ·
    right
    refine ⟨fun j => by fin_cases j <;> simp [hrow.1, hrow.2], fun i => ?_⟩
    obtain ⟨c, d, hcd⟩ := hx
    have hx1 : ∃ j, x 1 j ≠ 0 := by
      fin_cases c
      · fin_cases d
        · exact absurd hrow.1 hcd
        · exact absurd hrow.2 hcd
      · exact ⟨d, hcd⟩
    obtain ⟨j, hj⟩ := hx1
    have h := hF i j
    have hx0j : x 0 j = 0 := by fin_cases j; exacts [hrow.1, hrow.2]
    rw [hx0j, mul_zero, zero_add] at h
    exact (mul_eq_zero.1 h).resolve_right hj
  ·
    left
    have hdet : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 0 := by
      by_contra hd
      apply absurd hy
      push Not
      have hy0 : ∀ j, y 0 j = 0 := fun j => by
        have h1 := hE 0 j
        have h2 := hE 1 j
        have : (x 0 0 * x 1 1 - x 0 1 * x 1 0) * y 0 j = 0 := by linear_combination (x 1 1) * h1 - (x 0 1) * h2
        exact (mul_eq_zero.1 this).resolve_left hd
      have hy1 : ∀ j, y 1 j = 0 := fun j => by
        have h1 := hE 0 j
        have h2 := hE 1 j
        have : (x 0 0 * x 1 1 - x 0 1 * x 1 0) * y 1 j = 0 := by linear_combination (x 0 0) * h2 - (x 1 0) * h1
        exact (mul_eq_zero.1 this).resolve_left hd
      intro i j
      fin_cases i
      · exact hy0 j
      · exact hy1 j

    obtain ⟨t, ht⟩ : ∃ t : F, ∀ j, x 1 j = t * x 0 j := by
      by_cases h00 : x 0 0 = 0
      · have h01 : x 0 1 ≠ 0 := fun h => hrow ⟨h00, h⟩
        refine ⟨x 1 1 * (x 0 1)⁻¹, fun j => ?_⟩
        fin_cases j
        · have : x 0 1 * x 1 0 = 0 := by rw [h00, zero_mul, zero_sub, neg_eq_zero] at hdet; exact hdet
          simp [h00, (mul_eq_zero.1 this).resolve_left h01]
        · simp [mul_assoc, inv_mul_cancel₀ h01]
      · refine ⟨x 1 0 * (x 0 0)⁻¹, fun j => ?_⟩
        fin_cases j
        · simp [mul_assoc, inv_mul_cancel₀ h00]
        · field_simp
          simp only [Fin.mk_one, Fin.isValue]
          linear_combination hdet
    refine ⟨t, ht, fun i => ?_⟩
    have key : ∀ j, (y i 0 + t * y i 1) * x 0 j = 0 := fun j => by
      have h := hF i j
      rw [ht j] at h
      linear_combination h
    by_cases h00 : x 0 0 = 0
    · have h01 : x 0 1 ≠ 0 := fun h => hrow ⟨h00, h⟩
      exact (mul_eq_zero.1 (key 1)).resolve_right h01
    · exact (mul_eq_zero.1 (key 0)).resolve_right h00

theorem red_mul_apply {A B : M₂} (hA : A ∈ intMat q hq) (hB : B ∈ intMat q hq) (i j : Fin 2) :
    red q hq ((A * B) i j) = red q hq (A i 0) * red q hq (B 0 j) + red q hq (A i 1) * red q hq (B 1 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, red_add q hq (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j)),
    red_mul q hq (hA i 0) (hB 0 j), red_mul q hq (hA i 1) (hB 1 j)]

theorem red_smul_one_apply (i j : Fin 2) : red q hq ((ϖ • (1 : M₂)) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, red_mul q hq (q_mem_integers q hq) ((intMat q hq).one_mem i j), red_q,
    zero_mul]

theorem exists_red_ne_zero {A : M₂} (hA : A ∈ intMat q hq) (hn : ϖ⁻¹ • A ∉ intMat q hq) :
    ∃ i j, red q hq (A i j) ≠ 0 := by
  by_contra h
  push Not at h
  apply hn
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, q_inv_mul_mem_iff_red q hq (hA i j)]
  exact h i j

theorem repInv_some_mul (t : Fin q) (X : M₂) : repInv q hq (some t) * X =
    !![X 0 0, X 0 1;
      ϖ⁻¹ * (X 1 0 - ((t : ℕ) : 𝕂) * X 0 0), ϖ⁻¹ * (X 1 1 - ((t : ℕ) : 𝕂) * X 0 1)] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [repInv] <;> ring

theorem repInv_none_mul (X : M₂) : repInv q hq none * X =
    !![ϖ⁻¹ * X 0 0, ϖ⁻¹ * X 0 1; X 1 0, X 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [repInv]

theorem smul_mul_rep_some (t : Fin q) (Y : M₂) : ϖ⁻¹ • (Y * rep q hq (some t)) =
    !![ϖ⁻¹ * (Y 0 0 + ((t : ℕ) : 𝕂) * Y 0 1), Y 0 1;
      ϖ⁻¹ * (Y 1 0 + ((t : ℕ) : 𝕂) * Y 1 1), Y 1 1] := by
  have hq0 := q_ne_zero' q hq
  ext i j : 1
  rw [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp [rep, hq0, mul_comm]
  · simp [rep]; rw [mul_comm (Y 0 1), inv_mul_cancel_left₀ hq0]
  · simp [rep, hq0, mul_comm]
  · simp [rep]; rw [mul_comm (Y 1 1), inv_mul_cancel_left₀ hq0]

theorem smul_mul_rep_none (Y : M₂) : ϖ⁻¹ • (Y * rep q hq none) =
    !![Y 0 0, ϖ⁻¹ * Y 0 1; Y 1 0, ϖ⁻¹ * Y 1 1] := by
  have hq0 := q_ne_zero' q hq
  ext i j : 1
  rw [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp [rep]; rw [mul_comm (Y 0 0), inv_mul_cancel_left₀ hq0]
  · simp [rep]
  · simp [rep]; rw [mul_comm (Y 1 0), inv_mul_cancel_left₀ hq0]
  · simp [rep]

theorem exists_rep (X Y : M₂) (hX : X ∈ intMat q hq) (hY : Y ∈ intMat q hq)
    (hXY : X * Y = ϖ • (1 : M₂)) (hYX : Y * X = ϖ • (1 : M₂))
    (hYn : ϖ⁻¹ • Y ∉ intMat q hq) (hXn : ϖ⁻¹ • X ∉ intMat q hq) :
    ∃ o : Option (Fin q), repInv q hq o * X ∈ intMat q hq ∧ ϖ⁻¹ • (Y * rep q hq o) ∈ intMat q hq := by
  haveI : Fact q.Prime := ⟨hq⟩

  set x : Fin 2 → Fin 2 → ZMod q := fun i j => red q hq (X i j) with hx
  set y : Fin 2 → Fin 2 → ZMod q := fun i j => red q hq (Y i j) with hy
  have hE : ∀ i j, x i 0 * y 0 j + x i 1 * y 1 j = 0 := fun i j => by
    have h := congrArg (fun M : M₂ => red q hq (M i j)) hXY
    beta_reduce at h
    rwa [red_mul_apply q hq hX hY, red_smul_one_apply] at h
  have hF : ∀ i j, y i 0 * x 0 j + y i 1 * x 1 j = 0 := fun i j => by
    have h := congrArg (fun M : M₂ => red q hq (M i j)) hYX
    beta_reduce at h
    rwa [red_mul_apply q hq hY hX, red_smul_one_apply] at h
  have hyne : ∃ i j, y i j ≠ 0 := exists_red_ne_zero q hq hY hYn
  have hxne : ∃ i j, x i j ≠ 0 := exists_red_ne_zero q hq hX hXn
  rcases field_dichotomy x y hE hF hyne hxne with ⟨t, ht, hty⟩ | ⟨hx0, hy1⟩
  ·
    refine ⟨some ⟨t.val, t.val_lt⟩, ?_, ?_⟩
    · rw [repInv_some_mul]
      have hT : red q hq ((t.val : ℕ) : 𝕂) = t := red_natCast_val q hq t
      have hrow : ∀ j, ϖ⁻¹ * (X 1 j - ((t.val : ℕ) : 𝕂) * X 0 j) ∈ 𝓞v := fun j => by
        rw [q_inv_mul_mem_iff_red q hq (sub_mem (hX 1 j) (mul_mem (natCast_mem_integers _ _) (hX 0 j))),
          red_sub q hq (hX 1 j) (mul_mem (natCast_mem_integers _ _) (hX 0 j)),
          red_mul q hq (natCast_mem_integers _ _) (hX 0 j), hT, sub_eq_zero]
        exact ht j
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hX 0 0
      · simpa using hX 0 1
      · simpa using hrow 0
      · simpa using hrow 1
    · rw [smul_mul_rep_some]
      have hT : red q hq ((t.val : ℕ) : 𝕂) = t := red_natCast_val q hq t
      have hcol : ∀ i, ϖ⁻¹ * (Y i 0 + ((t.val : ℕ) : 𝕂) * Y i 1) ∈ 𝓞v := fun i => by
        rw [q_inv_mul_mem_iff_red q hq (add_mem (hY i 0) (mul_mem (natCast_mem_integers _ _) (hY i 1))),
          red_add q hq (hY i 0) (mul_mem (natCast_mem_integers _ _) (hY i 1)),
          red_mul q hq (natCast_mem_integers _ _) (hY i 1), hT]
        exact hty i
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hcol 0
      · simpa using hY 0 1
      · simpa using hcol 1
      · simpa using hY 1 1
  ·
    refine ⟨none, ?_, ?_⟩
    · rw [repInv_none_mul]
      have hrow : ∀ j, ϖ⁻¹ * X 0 j ∈ 𝓞v := fun j => by
        rw [q_inv_mul_mem_iff_red q hq (hX 0 j)]; exact hx0 j
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hrow 0
      · simpa using hrow 1
      · simpa using hX 1 0
      · simpa using hX 1 1
    · rw [smul_mul_rep_none]
      have hcol : ∀ i, ϖ⁻¹ * Y i 1 ∈ 𝓞v := fun i => by
        rw [q_inv_mul_mem_iff_red q hq (hY i 1)]; exact hy1 i
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hY 0 0
      · simpa using hcol 0
      · simpa using hY 1 0
      · simpa using hcol 1

end Local

section Model

variable {a b : ℚ} (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq))

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq) ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place q hq),
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))))
  (R : Submodule ℤ ℍ[ℚ, a, b])
  (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq),
    z ∈ Submodule.localBox R (place q hq) ↔ ∀ i j, φ z i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq))

omit hq φ R in

theorem ratCast_smul_eq_one_tmul_mul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    r • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

include hφ in
omit R in
theorem map_one_tmul_mul (c : 𝕂) (x : ℍv) : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := by
  rw [map_mul, hφ, smul_mul_assoc, one_mul]

include hφ in
omit R in

theorem map_natCast_smul (x : ℍv) : φ ((q : ℚ) • x) = ϖ • φ x := by
  rw [ratCast_smul_eq_one_tmul_mul, algebraMap_natCast, map_one_tmul_mul q hq φ hφ]

include hφ in
omit R in

theorem map_natCast_inv_smul (x : ℍv) : φ ((q : ℚ)⁻¹ • x) = ϖ⁻¹ • φ x := by
  rw [ratCast_smul_eq_one_tmul_mul, map_inv₀, algebraMap_natCast, map_one_tmul_mul q hq φ hφ]

def repUnit (o : Option (Fin q)) : (ℍv)ˣ where
  val := φ.symm (rep q hq o)
  inv := φ.symm (repInv q hq o)
  val_inv := by rw [← map_mul, rep_mul_repInv, map_one]
  inv_val := by rw [← map_mul, repInv_mul_rep, map_one]

omit R in
theorem coe_repUnit (o : Option (Fin q)) : ((repUnit q hq φ o : (ℍv)ˣ) : ℍv) = φ.symm (rep q hq o) := rfl

omit R in
theorem coe_repUnit_inv (o : Option (Fin q)) : (((repUnit q hq φ o)⁻¹ : (ℍv)ˣ) : ℍv) = φ.symm (repInv q hq o) := rfl

include hRv in

private theorem _root_.TqLoc.mem_stabilizer_iff (u : (ℍv)ˣ) :
    u ∈ MulAction.stabilizer (ℍv)ˣ
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ↔
      φ (u : ℍv) ∈ intMat q hq ∧ φ ((u⁻¹ : (ℍv)ˣ) : ℍv) ∈ intMat q hq := by
  have h1 : (1 : ℍv) ∈ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
    rw [SetLike.mem_coe, hRv, map_one]; exact (intMat q hq).one_mem

  have hsub : ∀ w : (ℍv)ˣ, φ (w : ℍv) ∈ intMat q hq →
      w • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ⊆
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
    rw [SetLike.mem_coe, hRv] at hy
    rw [Units.smul_def, smul_eq_mul, SetLike.mem_coe, hRv, map_mul]
    exact (intMat q hq).mul_mem hw hy
  constructor
  · intro hu
    rw [MulAction.mem_stabilizer_iff] at hu
    have hu' : u⁻¹ • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) =
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
      conv_lhs => rw [← hu]
      rw [inv_smul_smul]
    constructor
    · have : (u : ℍv) ∈ u • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) :=
        Set.mem_smul_set.2 ⟨1, h1, by rw [Units.smul_def, smul_eq_mul, mul_one]⟩
      rw [hu, SetLike.mem_coe, hRv] at this
      exact this
    · have : ((u⁻¹ : (ℍv)ˣ) : ℍv) ∈ u⁻¹ • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) :=
        Set.mem_smul_set.2 ⟨1, h1, by rw [Units.smul_def, smul_eq_mul, mul_one]⟩
      rw [hu', SetLike.mem_coe, hRv] at this
      exact this
  · rintro ⟨hu, hui⟩
    rw [MulAction.mem_stabilizer_iff]
    refine Set.Subset.antisymm (hsub u hu) fun x hx => ?_
    have hx' : u⁻¹ • x ∈ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) :=
      hsub u⁻¹ hui (Set.smul_mem_smul_set hx)
    exact Set.mem_smul_set.2 ⟨u⁻¹ • x, hx', smul_inv_smul u x⟩

p2m_export "TqLoc" "mem_stabilizer_iff"
include hRv in

theorem inv_mul_mem_stabilizer (g h : (ℍv)ˣ)
    (h1 : φ (((g⁻¹ : (ℍv)ˣ) : ℍv) * (h : ℍv)) ∈ intMat q hq)
    (h2 : φ (((h⁻¹ : (ℍv)ˣ) : ℍv) * (g : ℍv)) ∈ intMat q hq) :
    g⁻¹ * h ∈ MulAction.stabilizer (ℍv)ˣ
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
  rw [mem_stabilizer_iff q hq φ R hRv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  exact ⟨h1, h2⟩

def IsHecke (g : (ℍv)ˣ) : Prop :=
  (g : ℍv) ∈ Submodule.localBox R (place q hq) ∧
    (q : ℚ) • ((g⁻¹ : (ℍv)ˣ) : ℍv) ∈ Submodule.localBox R (place q hq) ∧
    ((g⁻¹ : (ℍv)ˣ) : ℍv) ∉ Submodule.localBox R (place q hq) ∧
    (q : ℚ)⁻¹ • (g : ℍv) ∉ Submodule.localBox R (place q hq)

include hφ hRv in

theorem local_of_isHecke (g : (ℍv)ˣ) (hg : IsHecke q hq R g) :
    φ (g : ℍv) ∈ intMat q hq ∧
    ϖ • φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) ∈ intMat q hq ∧
    φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) ∉ intMat q hq ∧
    ϖ⁻¹ • φ (g : ℍv) ∉ intMat q hq := by
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨(hRv _).1 hg1, ?_, fun hc => hg3 ((hRv _).2 hc), fun hc => hg4 ?_⟩
  · have := (hRv _).1 hg2
    rwa [map_natCast_smul q hq φ hφ] at this
  · rw [hRv, map_natCast_inv_smul q hq φ hφ]
    exact hc

include hφ hRv in

theorem isHecke_repUnit (o : Option (Fin q)) : IsHecke q hq R (repUnit q hq φ o) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRv, coe_repUnit, RingEquiv.apply_symm_apply]
    exact rep_mem_intMat q hq o
  · rw [hRv, map_natCast_smul q hq φ hφ, coe_repUnit_inv, RingEquiv.apply_symm_apply]
    exact smul_repInv_mem_intMat q hq o
  · rw [hRv, coe_repUnit_inv, RingEquiv.apply_symm_apply]
    exact repInv_notMem_intMat q hq o
  · rw [hRv, map_natCast_inv_smul q hq φ hφ, coe_repUnit, RingEquiv.apply_symm_apply]
    exact smul_rep_notMem_intMat q hq o

include hRv in

theorem repUnit_injective (o o' : Option (Fin q))
    (h : (repUnit q hq φ o)⁻¹ * repUnit q hq φ o' ∈
      MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv)) :
    o = o' := by
  rw [mem_stabilizer_iff q hq φ R hRv] at h
  have h1 := h.1
  rw [Units.val_mul, coe_repUnit_inv, coe_repUnit, ← map_mul, RingEquiv.apply_symm_apply] at h1
  exact eq_of_repInv_mul_rep_mem q hq o o' h1

include hφ hRv in

theorem exists_repUnit_inv_mul_mem (g : (ℍv)ˣ) (hg : IsHecke q hq R g) :
    ∃ o, (repUnit q hq φ o)⁻¹ * g ∈
      MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
  obtain ⟨hX, hY, hn1, hn2⟩ := local_of_isHecke q hq φ hφ R hRv g hg
  have hq0 := q_ne_zero' q hq
  set X : M₂ := φ (g : ℍv) with hXdef
  set Y : M₂ := ϖ • φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) with hYdef
  have hXY : X * Y = ϖ • (1 : M₂) := by
    rw [hXdef, hYdef, Matrix.mul_smul, ← map_mul, Units.mul_inv, map_one]
  have hYX : Y * X = ϖ • (1 : M₂) := by
    rw [hXdef, hYdef, Matrix.smul_mul, ← map_mul, Units.inv_mul, map_one]
  have hYn : ϖ⁻¹ • Y ∉ intMat q hq := by
    rw [hYdef, smul_smul, inv_mul_cancel₀ hq0, one_smul]; exact hn1
  obtain ⟨o, ho1, ho2⟩ := exists_rep q hq X Y hX hY hXY hYX hYn hn2
  refine ⟨o, inv_mul_mem_stabilizer q hq φ R hRv (repUnit q hq φ o) g ?_ ?_⟩
  · rw [coe_repUnit_inv, map_mul, RingEquiv.apply_symm_apply]
    exact ho1
  · rw [coe_repUnit, map_mul, RingEquiv.apply_symm_apply]
    have : φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) * rep q hq o = ϖ⁻¹ • (Y * rep q hq o) := by
      rw [hYdef, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hq0, one_smul]
    rw [this]; exact ho2

include hφ hRv in

theorem main :
    Nat.card {c : (ℍv)ˣ ⧸
        MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) //
      ∃ g : (ℍv)ˣ, IsHecke q hq R g ∧
        (QuotientGroup.mk g : (ℍv)ˣ ⧸
          MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv)) = c} =
      q + 1 := by
  classical
  let f : Option (Fin q) →
      {c : (ℍv)ˣ ⧸
          MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) //
        ∃ g : (ℍv)ˣ, IsHecke q hq R g ∧
          (QuotientGroup.mk g : (ℍv)ˣ ⧸
            MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv)) = c} :=
    fun o => ⟨QuotientGroup.mk (repUnit q hq φ o), repUnit q hq φ o, isHecke_repUnit q hq φ hφ R hRv o, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro o o' heq
      have heq' := congrArg Subtype.val heq
      exact repUnit_injective q hq φ R hRv o o' (QuotientGroup.eq.1 heq')
    · rintro ⟨c, g, hg, rfl⟩
      obtain ⟨o, ho⟩ := exists_repUnit_inv_mul_mem q hq φ hφ R hRv g hg
      exact ⟨o, Subtype.ext (QuotientGroup.eq.2 ho)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_fin]

end Model

end TqLoc

end

namespace TqLoc

section RepsOneCoset

variable (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq))

theorem exists_rep_eq_mul_rep_none_mul (o : Option (Fin q)) :
    ∃ k ki k' ki' : M₂, k ∈ intMat q hq ∧ ki ∈ intMat q hq ∧ k' ∈ intMat q hq ∧ ki' ∈ intMat q hq ∧
      k * ki = 1 ∧ ki * k = 1 ∧ k' * ki' = 1 ∧ ki' * k' = 1 ∧ rep q hq o = k * rep q hq none * k' := by
  have h1 : (1 : 𝕂) ∈ 𝓞v := one_mem _
  have h0 : (0 : 𝕂) ∈ 𝓞v := zero_mem _
  cases o with
  | none =>
    refine ⟨1, 1, 1, 1, (intMat q hq).one_mem, (intMat q hq).one_mem, (intMat q hq).one_mem, (intMat q hq).one_mem,
      mul_one _, mul_one _, mul_one _, mul_one _, ?_⟩
    rw [one_mul, mul_one]
  | some t =>
    have ht : (((t : ℕ) : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers (place q hq) _
    refine ⟨!![0, 1; 1, ((t : ℕ) : 𝕂)], !![-(((t : ℕ) : 𝕂)), 1; 1, 0], !![0, 1; 1, 0], !![0, 1; 1, 0],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_intMat_iff]; intro i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, ht]
    · rw [mem_intMat_iff]; intro i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, ht, neg_mem]
    · rw [mem_intMat_iff]; intro i j; fin_cases i <;> fin_cases j <;> simp [h0, h1]
    · rw [mem_intMat_iff]; intro i j; fin_cases i <;> fin_cases j <;> simp [h0, h1]
    · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [rep, Matrix.mul_apply, Fin.sum_univ_two]

end RepsOneCoset

section LocalDCT

variable {a b : ℚ} (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq) ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place q hq),
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))))
  (R : Submodule ℤ ℍ[ℚ, a, b])
  (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq),
    z ∈ Submodule.localBox R (place q hq) ↔ ∀ i j, φ z i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq))

noncomputable def unitOfIntMat (k ki : M₂) (h1 : k * ki = 1) (h2 : ki * k = 1) : (ℍv)ˣ where
  val := φ.symm k
  inv := φ.symm ki
  val_inv := by rw [← map_mul, h1, map_one]
  inv_val := by rw [← map_mul, h2, map_one]

include hRv in
theorem unitOfIntMat_mem_stabilizer (k ki : M₂) (hk : k ∈ intMat q hq) (hki : ki ∈ intMat q hq)
    (h1 : k * ki = 1) (h2 : ki * k = 1) :
    unitOfIntMat q hq φ k ki h1 h2 ∈ MulAction.stabilizer (ℍv)ˣ
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
  rw [mem_stabilizer_iff q hq φ R hRv]
  show φ (φ.symm k) ∈ intMat q hq ∧ φ (φ.symm ki) ∈ intMat q hq
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact ⟨hk, hki⟩

include hφ hRv in

theorem exists_repUnit_eq (o : Option (Fin q)) :
    ∃ k k' : (ℍv)ˣ, k ∈ MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ∧
      k' ∈ MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ∧
      repUnit q hq φ o = k * repUnit q hq φ none * k' := by
  obtain ⟨k, ki, k', ki', hk, hki, hk', hki', h1, h2, h3, h4, heq⟩ := exists_rep_eq_mul_rep_none_mul q hq o
  refine ⟨unitOfIntMat q hq φ k ki h1 h2, unitOfIntMat q hq φ k' ki' h3 h4,
    unitOfIntMat_mem_stabilizer q hq φ R hRv k ki hk hki h1 h2,
    unitOfIntMat_mem_stabilizer q hq φ R hRv k' ki' hk' hki' h3 h4, ?_⟩
  apply Units.ext
  show φ.symm (rep q hq o) = φ.symm k * φ.symm (rep q hq none) * φ.symm k'
  rw [← map_mul, ← map_mul, ← heq]

include hφ hRv in

theorem exists_eq_mul_mul_of_isHecke (g h : (ℍv)ˣ) (hg : IsHecke q hq R g) (hh : IsHecke q hq R h) :
    ∃ k k' : (ℍv)ˣ, k ∈ MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ∧
      k' ∈ MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ∧
      h = k * g * k' := by
  obtain ⟨o, ho⟩ := exists_repUnit_inv_mul_mem q hq φ hφ R hRv g hg
  obtain ⟨o', ho'⟩ := exists_repUnit_inv_mul_mem q hq φ hφ R hRv h hh
  obtain ⟨k₁, k₁', hk₁, hk₁', e₁⟩ := exists_repUnit_eq q hq φ hφ R hRv o
  obtain ⟨k₂, k₂', hk₂, hk₂', e₂⟩ := exists_repUnit_eq q hq φ hφ R hRv o'

  set s₁ := (repUnit q hq φ o)⁻¹ * g with hs₁
  set s₂ := (repUnit q hq φ o')⁻¹ * h with hs₂
  have hg' : g = k₁ * repUnit q hq φ none * k₁' * s₁ := by rw [hs₁, ← e₁]; group
  have hh' : h = k₂ * repUnit q hq φ none * k₂' * s₂ := by rw [hs₂, ← e₂]; group
  refine ⟨k₂ * k₁⁻¹, s₁⁻¹ * k₁'⁻¹ * k₂' * s₂, mul_mem hk₂ (inv_mem hk₁),
    mul_mem (mul_mem (mul_mem (inv_mem ho) (inv_mem hk₁')) hk₂') ho', ?_⟩
  rw [hh', hg']; group

end LocalDCT

end TqLoc

open TqLoc in
theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓq' : ℓ ≠ q')
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hg : g ∈ QuaternionAlgebra.primeHeckeSet R ℓ) :
    QuaternionAlgebra.primeHeckeSet R ℓ =
      DoubleCoset.doubleCoset g (Submodule.finiteIdeleStabilizer R) (Submodule.finiteIdeleStabilizer R) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq' : q'.Prime := Fact.out
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder

  have hq'v : (q' : 𝓞 ℚ) ∉ (place ℓ hℓ).asIdeal := by
    rw [natCast_mem_asIdeal_place_iff]
    exact fun h => hℓq' ((Nat.prime_dvd_prime_iff_eq hℓ hq').1 h)
  have hNv : (N : 𝓞 ℚ) ∉ (place ℓ hℓ).asIdeal := by
    rw [natCast_mem_asIdeal_place_iff]; exact hℓN
  obtain ⟨φ, hφ, hRv⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef hR (place ℓ hℓ) hq'v hNv
  have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (place ℓ hℓ).asIdeal := (natCast_mem_asIdeal_place_iff ℓ hℓ ℓ).mpr dvd_rfl
  apply Set.Subset.antisymm
  ·
    intro h hh
    have hoffg : C4T.OffUnit R (place ℓ hℓ) g := C4T.offUnit_of_mem_primeHeckeSet hℓ hℓv hg
    have hoffh : C4T.OffUnit R (place ℓ hℓ) h := C4T.offUnit_of_mem_primeHeckeSet hℓ hℓv hh
    have hgloc : IsHecke ℓ hℓ R (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place ℓ hℓ)).toRingHom.toMonoidHom g) :=
      (C4T.mem_primeHeckeSet_iff_local hRo hℓ hℓv hoffg).mp hg
    have hhloc : IsHecke ℓ hℓ R (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place ℓ hℓ)).toRingHom.toMonoidHom h) :=
      (C4T.mem_primeHeckeSet_iff_local hRo hℓ hℓv hoffh).mp hh
    obtain ⟨k, k', hk, hk', hloc⟩ := exists_eq_mul_mul_of_isHecke ℓ hℓ φ hφ R hRv _ _ hgloc hhloc

    obtain ⟨uL, huLv, huLoff⟩ := C4T.exists_offUnit_map_eq hRo (place ℓ hℓ) k
    have h1off : C4T.OffUnit R (place ℓ hℓ) 1 := fun w _ => by rw [map_one]; exact C4T.one_mem_localBoxUnits hRo w
    have huL : uL ∈ Submodule.finiteIdeleStabilizer R := by
      have := C4T.inv_mul_mem_finiteIdeleStabilizer_of_local hRo h1off huLoff (by rw [map_one, inv_one, one_mul, huLv]; exact hk)
      rwa [inv_one, one_mul] at this

    have hoff' : C4T.OffUnit R (place ℓ hℓ) (uL⁻¹ * h) := fun w hw => by
      rw [map_mul, map_inv]; exact C4T.mul_mem_localBoxUnits hRo w (C4T.inv_mem_localBoxUnits w (huLoff w hw)) (hoffh w hw)
    have hu' : g⁻¹ * (uL⁻¹ * h) ∈ Submodule.finiteIdeleStabilizer R := by
      refine C4T.inv_mul_mem_finiteIdeleStabilizer_of_local hRo hoffg hoff' ?_
      rw [map_mul, map_inv, huLv, hloc]
      rw [show (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place ℓ hℓ)).toRingHom.toMonoidHom g)⁻¹ *
          (k⁻¹ * (k * Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place ℓ hℓ)).toRingHom.toMonoidHom g * k')) = k' from by group]
      exact hk'
    refine DoubleCoset.mem_doubleCoset.mpr ⟨uL, huL, g⁻¹ * (uL⁻¹ * h), hu', ?_⟩
    group
  ·
    intro x hx
    obtain ⟨u, hu, u', hu', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer' hRo ℓ hu' (HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer hRo ℓ hu hg)

end S_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
end P2MW
export P2MW.S_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer (solution)
