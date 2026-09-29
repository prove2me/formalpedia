-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b2f1d1d1-3662-51a2-9f14-cd184611c665

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "prime_iff card_eq_fintype_card count card_eq_zero cast_sum Coprime choose cast_eq_zero Prime prime_iff_prime_int isCoprime_iff_coprime eq_zero_or_pos cast_zero castRingHom card_congr zero cast_one"
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

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace K1a

open Classical in
noncomputable scoped instance : DecidableEq (HeightOneSpectrum (𝓞 ℚ)) := Classical.decEq _

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

def IsSupportedOn (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (β : (ℍ𝔸)ˣ) : Prop :=
  ∀ v ∉ S, (ev v) (β : ℍ𝔸) = 1

theorem commute_of_isSupportedOn {S S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hSS' : Disjoint S S')
    {β β' : (ℍ𝔸)ˣ} (hβ : IsSupportedOn S β) (hβ' : IsSupportedOn S' β') : β * β' = β' * β := by
  apply Units.ext
  apply Submodule.eq_of_forall_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b])
  intro v
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  by_cases hv : v ∈ S
  · rw [hβ' v (Finset.disjoint_left.mp hSS' hv), mul_one, one_mul]
  · rw [hβ v hv, one_mul, mul_one]

theorem coe_unitsMap (v : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ𝔸)ˣ) :
    ((Units.map (ev v).toRingHom.toMonoidHom x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = (ev v) (x : ℍ𝔸) := rfl

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v := by
  rw [Submodule.mem_localBoxUnits_iff]
  exact ⟨HeckeLocal.one_mem_localBox hΛ v, by simpa using HeckeLocal.one_mem_localBox hΛ v⟩

theorem exists_isSupportedOn_mul_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    ∃ β u : (ℍ𝔸)ˣ, u ∈ Submodule.finiteIdeleStabilizer Λ ∧ h = β * u ∧ IsSupportedOn (Nat.placesOf ℓ) β := by
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) (Nat.placesOf ℓ)
    (fun v => Units.map (ev v).toRingHom.toMonoidHom h)
  refine ⟨β, β⁻¹ * h, ?_, by rw [mul_inv_cancel_left], h2⟩
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ]
  intro v
  rw [map_mul, map_inv]
  by_cases hv : v ∈ Nat.placesOf ℓ
  · have : Units.map (ev v).toRingHom.toMonoidHom β = Units.map (ev v).toRingHom.toMonoidHom h :=
      Units.ext (h1 v hv)
    rw [this, inv_mul_cancel]
    exact one_mem_localBoxUnits hΛ v
  · have : Units.map (ev v).toRingHom.toMonoidHom β = 1 := Units.ext (h2 v hv)
    rw [this, inv_one, one_mul]
    exact HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ hh v
      (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ hv)

theorem exists_rep {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {T : Set (ℍ𝔸)ˣ} (hT : T ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (hTr : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T, s * u ∈ T) :
    ∃ r : ((ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) → (ℍ𝔸)ˣ,
      ∀ c, (∃ h ∈ T, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c) →
        r c ∈ T ∧ (r c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c ∧ IsSupportedOn (Nat.placesOf ℓ) (r c) := by
  classical
  have key : ∀ c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ, (∃ h ∈ T, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c) →
      ∃ β : (ℍ𝔸)ˣ, β ∈ T ∧ (β : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c ∧ IsSupportedOn (Nat.placesOf ℓ) β := by
    rintro c ⟨h, hhT, rfl⟩
    obtain ⟨β, u, hu, rfl, hβ⟩ := exists_isSupportedOn_mul_eq hΛ hℓ (hT hhT)
    refine ⟨β, ?_, ?_, hβ⟩
    · have := hTr u⁻¹ (inv_mem hu) _ hhT
      rwa [mul_inv_cancel_right] at this
    · exact (QuotientGroup.mk_mul_of_mem β hu).symm
  refine ⟨fun c => if hc : _ then (key c hc).choose else 1, fun c hc => ?_⟩
  simp only [dif_pos hc]
  exact (key c hc).choose_spec

section Count

theorem natCard_heckeIncidence_eq_card_filter (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [DecidableEq (QuaternionAlgebra.ClassSet U)] (S : Set (ℍ𝔸)ˣ) (CS : Finset ((ℍ𝔸)ˣ ⧸ U))
    (hCS : ∀ c, c ∈ CS ↔ ∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ U) = c)
    (r : ((ℍ𝔸)ˣ ⧸ U) → (ℍ𝔸)ˣ) (hr : ∀ c ∈ CS, r c ∈ S ∧ (r c : (ℍ𝔸)ˣ ⧸ U) = c)
    (x : (ℍ𝔸)ˣ) (y : QuaternionAlgebra.ClassSet U) :
    Nat.card (QuaternionAlgebra.HeckeIncidence U S x y) =
      (CS.filter fun c => QuaternionAlgebra.ClassSet.mk U (x * r c) = y).card := by
  classical
  have hiff : ∀ c : (ℍ𝔸)ˣ ⧸ U, (∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ U) = c ∧ QuaternionAlgebra.ClassSet.mk U (x * h) = y) ↔
      c ∈ CS.filter fun c => QuaternionAlgebra.ClassSet.mk U (x * r c) = y := by
    intro c
    rw [Finset.mem_filter, hCS]
    constructor
    · rintro ⟨h, hS, hc, hy⟩
      refine ⟨⟨h, hS, hc⟩, ?_⟩
      obtain ⟨-, hrc⟩ := hr c ((hCS c).mpr ⟨h, hS, hc⟩)

      have hu : h⁻¹ * r c ∈ U := QuotientGroup.eq.mp (hc.trans hrc.symm)
      have : r c = h * (h⁻¹ * r c) := by rw [mul_inv_cancel_left]
      rw [this, ← mul_assoc, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ hu, hy]
    · rintro ⟨hc, hy⟩
      obtain ⟨hS, hrc⟩ := hr c ((hCS c).mpr hc)
      exact ⟨r c, hS, hrc, hy⟩
  unfold QuaternionAlgebra.HeckeIncidence
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem classSetHeckeMatrix_apply (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [DecidableEq (QuaternionAlgebra.ClassSet U)] (S : Set (ℍ𝔸)ˣ) (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S) (CS : Finset ((ℍ𝔸)ˣ ⧸ U))
    (hCS : ∀ c, c ∈ CS ↔ ∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ U) = c)
    (r : ((ℍ𝔸)ˣ ⧸ U) → (ℍ𝔸)ˣ) (hr : ∀ c ∈ CS, r c ∈ S ∧ (r c : (ℍ𝔸)ˣ ⧸ U) = c)
    (x : (ℍ𝔸)ˣ) (i : QuaternionAlgebra.ClassSet U) :
    CerednikDrinfeld.classSetHeckeMatrix U S i (QuaternionAlgebra.ClassSet.mk U x) =
      ((CS.filter fun c => QuaternionAlgebra.ClassSet.mk U (x * r c) = i).card : ℤ) := by
  classical
  rw [CerednikDrinfeld.classSetHeckeMatrix, Matrix.of_apply, QuaternionAlgebra.heckeKernel_mk U S hS x i,
    natCard_heckeIncidence_eq_card_filter U S CS hCS r hr x i]

theorem mul_apply_eq (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (QuaternionAlgebra.ClassSet U)] [DecidableEq (QuaternionAlgebra.ClassSet U)] (S S' : Set (ℍ𝔸)ˣ) (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (CS CS' : Finset ((ℍ𝔸)ˣ ⧸ U))
    (hCS : ∀ c, c ∈ CS ↔ ∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ U) = c) (hCS' : ∀ c, c ∈ CS' ↔ ∃ h ∈ S', (h : (ℍ𝔸)ˣ ⧸ U) = c)
    (r r' : ((ℍ𝔸)ˣ ⧸ U) → (ℍ𝔸)ˣ) (hr : ∀ c ∈ CS, r c ∈ S ∧ (r c : (ℍ𝔸)ˣ ⧸ U) = c)
    (hr' : ∀ c ∈ CS', r' c ∈ S' ∧ (r' c : (ℍ𝔸)ˣ ⧸ U) = c)
    (i k : QuaternionAlgebra.ClassSet U) :
    (CerednikDrinfeld.classSetHeckeMatrix U S * CerednikDrinfeld.classSetHeckeMatrix U S') i k =
      ∑ c' ∈ CS', ((CS.filter fun c => QuaternionAlgebra.ClassSet.mk U (k.out * r' c' * r c) = i).card : ℤ) := by
  classical
  rw [Matrix.mul_apply]

  have h2 : ∀ j, CerednikDrinfeld.classSetHeckeMatrix U S' j k =
      ((CS'.filter fun c' => QuaternionAlgebra.ClassSet.mk U (k.out * r' c') = j).card : ℤ) := by
    intro j
    rw [CerednikDrinfeld.classSetHeckeMatrix, Matrix.of_apply, QuaternionAlgebra.heckeKernel,
      natCard_heckeIncidence_eq_card_filter U S' CS' hCS' r' hr' k.out j]
  simp_rw [h2]

  have step : ∑ j, CerednikDrinfeld.classSetHeckeMatrix U S i j *
      ((CS'.filter fun c' => QuaternionAlgebra.ClassSet.mk U (k.out * r' c') = j).card : ℤ) =
      ∑ c' ∈ CS', CerednikDrinfeld.classSetHeckeMatrix U S i (QuaternionAlgebra.ClassSet.mk U (k.out * r' c')) := by
    rw [← Finset.sum_fiberwise CS' (fun c' => QuaternionAlgebra.ClassSet.mk U (k.out * r' c'))
      (fun c' => CerednikDrinfeld.classSetHeckeMatrix U S i (QuaternionAlgebra.ClassSet.mk U (k.out * r' c')))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' hc' => ?_
    rw [(Finset.mem_filter.mp hc').2, Nat.cast_one, mul_one]
  rw [step]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [classSetHeckeMatrix_apply U S hS CS hCS r hr]

end Count

section Final

theorem primeHeckeSet_zero (Λ : Submodule ℤ ℍ[ℚ, a, b]) : QuaternionAlgebra.primeHeckeSet Λ 0 = ∅ := by
  ext h
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, -, h4⟩
  apply h4
  rw [Nat.cast_zero, inv_zero, zero_smul]
  exact zero_mem _

theorem classSetHeckeMatrix_empty (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetHeckeMatrix U (∅ : Set (ℍ𝔸)ˣ) = 0 := by
  ext i j
  rw [CerednikDrinfeld.classSetHeckeMatrix, Matrix.of_apply, Matrix.zero_apply, QuaternionAlgebra.heckeKernel,
    Nat.cast_eq_zero, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨c, h, hh, -⟩
  exact hh

theorem sum_card_filter_comm (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [DecidableEq (QuaternionAlgebra.ClassSet U)]
    (CS CS' : Finset ((ℍ𝔸)ˣ ⧸ U)) (r r' : ((ℍ𝔸)ˣ ⧸ U) → (ℍ𝔸)ˣ)
    (hcomm : ∀ c ∈ CS, ∀ c' ∈ CS', r c * r' c' = r' c' * r c) (x : (ℍ𝔸)ˣ) (i : QuaternionAlgebra.ClassSet U) :
    ∑ c' ∈ CS', ((CS.filter fun c => QuaternionAlgebra.ClassSet.mk U (x * r' c' * r c) = i).card : ℤ) =
      ∑ c ∈ CS, ((CS'.filter fun c' => QuaternionAlgebra.ClassSet.mk U (x * r c * r' c') = i).card : ℤ) := by
  simp_rw [Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun c' hc' => ?_
  rw [mul_assoc, ← hcomm c hc c' hc', ← mul_assoc]

end Final

end K1a
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime.K1a"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer Λ))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer Λ))]
    (ℓ ℓ' : ℕ) (hℓ : ℓ.Coprime ℓ')
    (T T' : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hT : T ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ) (hT' : T' ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ')
    (hTl : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T, u * s ∈ T)
    (hTr : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T, s * u ∈ T)
    (hT'l : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T', u * s ∈ T')
    (hT'r : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T', s * u ∈ T')

    (hTfin : {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ | ∃ h ∈ T,
      (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c}.Finite)
    (hT'fin : {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ | ∃ h ∈ T',
      (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c}.Finite) :
    Commute (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer Λ) T)
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer Λ) T') := by
  classical

  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have : T = ∅ := Set.subset_eq_empty (hT.trans (K1a.primeHeckeSet_zero Λ).le) rfl
    rw [this, K1a.classSetHeckeMatrix_empty]
    exact Commute.zero_left _
  by_cases hℓ0' : ℓ' = 0
  · subst hℓ0'
    have : T' = ∅ := Set.subset_eq_empty (hT'.trans (K1a.primeHeckeSet_zero Λ).le) rfl
    rw [this, K1a.classSetHeckeMatrix_empty]
    exact Commute.zero_right _

  have hCS : ∀ c, c ∈ hTfin.toFinset ↔ ∃ h ∈ T, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ (Submodule.finiteIdeleStabilizer Λ)) = c :=
    fun c => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hCS' : ∀ c, c ∈ hT'fin.toFinset ↔ ∃ h ∈ T', (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ (Submodule.finiteIdeleStabilizer Λ)) = c :=
    fun c => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨r, hr⟩ := K1a.exists_rep hΛ hℓ0 hT hTr
  obtain ⟨r', hr'⟩ := K1a.exists_rep hΛ hℓ0' hT' hT'r
  have hr1 : ∀ c ∈ hTfin.toFinset, r c ∈ T ∧ (r c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ (Submodule.finiteIdeleStabilizer Λ)) = c :=
    fun c hc => ⟨(hr c ((hCS c).mp hc)).1, (hr c ((hCS c).mp hc)).2.1⟩
  have hr1' : ∀ c ∈ hT'fin.toFinset, r' c ∈ T' ∧ (r' c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ (Submodule.finiteIdeleStabilizer Λ)) = c :=
    fun c hc => ⟨(hr' c ((hCS' c).mp hc)).1, (hr' c ((hCS' c).mp hc)).2.1⟩
  have hcomm : ∀ c ∈ hTfin.toFinset, ∀ c' ∈ hT'fin.toFinset, r c * r' c' = r' c' * r c := fun c hc c' hc' =>
    K1a.commute_of_isSupportedOn (Nat.disjoint_placesOf_of_coprime hℓ0 hℓ0' hℓ)
      (hr c ((hCS c).mp hc)).2.2 (hr' c' ((hCS' c').mp hc')).2.2

  refine Matrix.ext fun i k => ?_
  rw [K1a.mul_apply_eq (Submodule.finiteIdeleStabilizer Λ) T T' hTl _ _ hCS hCS' r r' hr1 hr1' i k,
    K1a.mul_apply_eq (Submodule.finiteIdeleStabilizer Λ) T' T hT'l _ _ hCS' hCS r' r hr1' hr1 i k]
  exact K1a.sum_card_filter_comm (Submodule.finiteIdeleStabilizer Λ) _ _ r r' hcomm k.out i

end S_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime (solution)
