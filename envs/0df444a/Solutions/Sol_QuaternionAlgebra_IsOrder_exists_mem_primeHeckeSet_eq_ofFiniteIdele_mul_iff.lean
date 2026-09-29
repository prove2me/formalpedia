-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4c7a9dae-4021-5b5e-af12-ee27b967ce86

import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_PadicInt_natCard_quotient_range_eq_pow_valuation_det
import Theorems.Thm_Submodule_fg_and_span_eq_top_ofFiniteIdele
import Theorems.Thm_Submodule_mem_localBox_ofFiniteIdele_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace Ws43E7

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

theorem box_smul_le (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℚ) {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    q • x ∈ Submodule.finiteAdeleBox (q • Λ) := by
  unfold Submodule.finiteAdeleBox at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨q • z, Submodule.smul_mem_pointwise_smul z q Λ hz, c, hc, ?_⟩
    rw [TensorProduct.smul_tmul']
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem isLattice_ofFiniteIdele {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (g : (ℍ𝔸)ˣ) : Submodule.IsLattice ℚ (Submodule.ofFiniteIdele R g) :=
  let h := Submodule.fg_and_span_eq_top_ofFiniteIdele R hR.fg hR.spanTop g
  ⟨h.1, h.2⟩

theorem localBox_ofFiniteIdele_eq_map {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (g : (ℍ𝔸)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox (Submodule.ofFiniteIdele R g) v =
      (Submodule.localBox R v).map
        (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : ℍ𝔸))) := by
  ext x
  rw [Submodule.mem_localBox_ofFiniteIdele_iff R hR.fg hR.spanTop g v x, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem heightOneSpectrum_eq_of_natPrime_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (hw : (ℓ : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), (ℓ : 𝓞 ℚ) ∈ u.asIdeal →
      Rat.HeightOneSpectrum.natGenerator u = ℓ := by
    intro u hu
    have hdvd : Rat.HeightOneSpectrum.natGenerator u ∣ ℓ := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hu
      rwa [map_natCast] at this
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator u) hℓ).mp hdvd
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext ((key v hv).trans (key w hw).symm)

theorem inv_natCast_mem_adicCompletionIntegers {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ))
    (hw : (ℓ : 𝓞 ℚ) ∉ w.asIdeal) :
    algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hval : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = w.valuation ℚ ((ℓ : ℚ)⁻¹) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((ℓ : ℚ)⁻¹)
  rw [hval, map_inv₀]
  have hℓ' : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
  rw [hℓ', HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hw,
    inv_one]

theorem evalAt_inv_mem_localBox {R : Submodule ℤ ℍ[ℚ, a, b]} {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) {h : (ℍ𝔸)ˣ}
    (h2 : (ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hℓw : algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w := by
  have hℓq : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ0
  have e : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) *
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul,
      inv_mul_cancel₀ hℓq, one_smul]
  rw [e]
  exact tmul_one_mul_mem_localBox w hℓw (finiteAdeleEvalAt_mem_localBox w h2)

theorem relIndex_localBox_eq_one_of_not_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) (x h : (ℍ𝔸)ˣ)
    (h1 : (h : ℍ𝔸) ∈ Submodule.finiteAdeleBox R)
    (h2 : (ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∉ v.asIdeal) :
    (Submodule.localBox (Submodule.ofFiniteIdele R (x * h)) v).relIndex
      (Submodule.localBox (Submodule.ofFiniteIdele R x) v) = 1 := by
  set f := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hf
  have hu : f (h : ℍ𝔸) ∈ Submodule.localBox R v := finiteAdeleEvalAt_mem_localBox v h1
  have hui : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R v :=
    evalAt_inv_mem_localBox hℓ0 h2 v (inv_natCast_mem_adicCompletionIntegers hℓ0 v hv)

  have hfix : (Submodule.localBox R v).map (AddMonoidHom.mulLeft (f (h : ℍ𝔸))) = Submodule.localBox R v := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact localBox_mul_mem hR v hu hr
    · intro r hr
      refine ⟨f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * r, localBox_mul_mem hR v hui hr, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have heq : Submodule.localBox (Submodule.ofFiniteIdele R (x * h)) v =
      Submodule.localBox (Submodule.ofFiniteIdele R x) v := by
    rw [localBox_ofFiniteIdele_eq_map hR, localBox_ofFiniteIdele_eq_map hR, Units.val_mul, map_mul]
    conv_lhs => rw [show AddMonoidHom.mulLeft (f (x : ℍ𝔸) * f (h : ℍ𝔸)) =
        (AddMonoidHom.mulLeft (f (x : ℍ𝔸))).comp (AddMonoidHom.mulLeft (f (h : ℍ𝔸))) from by
          ext y; simp [mul_assoc], ← AddSubgroup.map_map, hfix]
  rw [heq, AddSubgroup.relIndex_self]

theorem relIndex_map_mulLeft_of_leftInverse {S : Type*} [Ring S] (u w : S) (huw : w * u = 1) (A B : AddSubgroup S) :
    (A.map (AddMonoidHom.mulLeft u)).relIndex (B.map (AddMonoidHom.mulLeft u)) = A.relIndex B := by
  apply AddSubgroup.relIndex_map_map_of_injective
  intro p q hpq
  have : u * p = u * q := hpq
  have := congrArg (fun z => w * z) this
  simpa only [← mul_assoc, huw, one_mul] using this

theorem ringEquiv_map_ratSmul (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (q : ℚ) (z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    φ (q • z) = (algebraMap ℚ (v.adicCompletion ℚ) q) • φ z := by
  have e : q • z = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) q) * z := by
    rw [← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def]
  rw [e, map_mul, hφ, smul_mul_assoc, one_mul]

theorem relIndex_localBox_ofFiniteIdele_mul {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (x h : (ℍ𝔸)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox (Submodule.ofFiniteIdele R (x * h)) v).relIndex
        (Submodule.localBox (Submodule.ofFiniteIdele R x) v) =
      ((Submodule.localBox R v).map
          (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)))).relIndex
        (Submodule.localBox R v) := by
  rw [localBox_ofFiniteIdele_eq_map hR, localBox_ofFiniteIdele_eq_map hR, Units.val_mul, map_mul]
  have hcomp : AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ𝔸) *
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)) =
      (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ𝔸))).comp
        (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸))) := by
    ext y; simp [mul_assoc]
  rw [hcomp, ← AddSubgroup.map_map]
  refine relIndex_map_mulLeft_of_leftInverse _ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ?_ _ _
  rw [← map_mul, Units.inv_mul, map_one]

theorem det_mulLeft_fin_two {R : Type*} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R) :
    LinearMap.det (LinearMap.mulLeft R h) = h.det ^ 2 := by
  classical
  set b := Matrix.stdBasis R (Fin 2) (Fin 2) with hb
  have key : Matrix.toLin b b (Matrix.blockDiagonal fun _ : Fin 2 => h) = LinearMap.mulLeft R h := by
    refine b.ext fun jk => ?_
    obtain ⟨k, l'⟩ := jk
    rw [Matrix.toLin_self, LinearMap.mulLeft_apply]
    ext i l
    simp only [hb, Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.stdBasis_eq_single, Matrix.blockDiagonal_apply', Matrix.mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases k <;> fin_cases l <;> fin_cases l' <;> simp [Matrix.single_apply]
  rw [← key, LinearMap.det_toLin, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

section C1
variable (p : ℕ) [Fact p.Prime]

theorem PadicInt.isUnit_iff_valuation_eq_zero {z : ℤ_[p]} (hz : z ≠ 0) :
    IsUnit z ↔ z.valuation = 0 := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_eq_zpow_neg_valuation hz]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [zpow_eq_one_iff_right₀ (zero_le_one.trans hp.le) hp.ne']
  omega

theorem natCard_quotient_range_mulLeft (h : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hh : h.det ≠ 0) :
    Nat.card (Matrix (Fin 2) (Fin 2) ℤ_[p] ⧸ LinearMap.range (LinearMap.mulLeft ℤ_[p] h)) =
      p ^ (2 * h.det.valuation) := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℤ_[p] h) = h.det ^ 2 := det_mulLeft_fin_two h
  have hne : LinearMap.det (LinearMap.mulLeft ℤ_[p] h) ≠ 0 := by rw [hdet]; exact pow_ne_zero _ hh
  rw [PadicInt.natCard_quotient_range_eq_pow_valuation_det p _ hne, hdet, PadicInt.valuation_pow]

theorem natCard_quotient_range_mulLeft_eq_sq_iff (h k : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hhk : h * k = (p : ℤ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[p])) :
    Nat.card (Matrix (Fin 2) (Fin 2) ℤ_[p] ⧸ LinearMap.range (LinearMap.mulLeft ℤ_[p] h)) = p ^ 2 ↔
      (¬ IsUnit h ∧ ¬ IsUnit k) := by
  have hp : (p : ℤ_[p]) ≠ 0 := NeZero.ne _
  have hdetprod : h.det * k.det = (p : ℤ_[p]) ^ 2 := by
    rw [← Matrix.det_mul, hhk, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hp2 : ((p : ℤ_[p]) ^ 2) ≠ 0 := pow_ne_zero _ hp
  have hh : h.det ≠ 0 := fun h0 => hp2 (by rw [← hdetprod, h0, zero_mul])
  have hk : k.det ≠ 0 := fun h0 => hp2 (by rw [← hdetprod, h0, mul_zero])
  have hsum : h.det.valuation + k.det.valuation = 2 := by
    have := congrArg PadicInt.valuation hdetprod
    rwa [PadicInt.valuation_mul hh hk, PadicInt.valuation_pow, PadicInt.valuation_p, mul_one] at this
  rw [natCard_quotient_range_mulLeft p h hh, Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    PadicInt.isUnit_iff_valuation_eq_zero p hh, PadicInt.isUnit_iff_valuation_eq_zero p hk]
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  constructor
  · intro h2
    have := Nat.pow_right_injective hp1 h2
    omega
  · rintro ⟨h1, h2⟩
    congr 1
    omega

end C1

theorem isUnit_map_ringEquiv_iff {S T : Type*} [Ring S] [Ring T] (ψ : S ≃+* T) (x : S) :
    IsUnit (ψ x) ↔ IsUnit x :=
  ⟨fun hu => by simpa using hu.map ψ.symm, fun hu => hu.map ψ⟩

section IntModel

variable (v : HeightOneSpectrum (𝓞 ℚ))

noncomputable def intMatrixEmb :
    Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) →+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).mapMatrix

theorem intMatrixEmb_apply (A : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)) (i j : Fin 2) :
    intMatrixEmb v A i j = ((A i j : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := rfl

theorem intMatrixEmb_injective : Function.Injective (intMatrixEmb v) := by
  intro A B hAB
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun hAB i) j
  rw [intMatrixEmb_apply, intMatrixEmb_apply] at hij
  exact Subtype.ext hij

theorem exists_intMatrixEmb_eq_iff (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    (∃ A, intMatrixEmb v A = M) ↔ ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨A, rfl⟩ i j
    exact (A i j).2
  · intro hM
    refine ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, ?_⟩
    ext i j; rfl

theorem isUnit_iff_inverse_integral (XO : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (h1 : intMatrixEmb v XO * Y = 1) (h2 : Y * intMatrixEmb v XO = 1) :
    IsUnit XO ↔ ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ := by
  rw [← exists_intMatrixEmb_eq_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨((u⁻¹ : (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))ˣ) : Matrix (Fin 2) (Fin 2) _), ?_⟩
    have h3 : intMatrixEmb v ((u⁻¹ : (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))ˣ) : Matrix (Fin 2) (Fin 2) _) *
        intMatrixEmb v XO = 1 := by
      rw [← hu, ← map_mul, Units.inv_mul, map_one]
    calc intMatrixEmb v ((u⁻¹ : (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))ˣ) : Matrix (Fin 2) (Fin 2) _)
        = intMatrixEmb v ((u⁻¹ : (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))ˣ) : Matrix (Fin 2) (Fin 2) _) *
            (intMatrixEmb v XO * Y) := by rw [h1, mul_one]
      _ = Y := by rw [← mul_assoc, h3, one_mul]
  · rintro ⟨UO, hUO⟩
    refine ⟨⟨XO, UO, intMatrixEmb_injective v ?_, intMatrixEmb_injective v ?_⟩, rfl⟩
    · rw [map_mul, hUO, h1, map_one]
    · rw [map_mul, hUO, h2, map_one]

theorem relIndex_map_mulLeft_eq_index
    (L : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hL : ∀ M, M ∈ L ↔ ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ)
    (HO : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)) :
    (L.map (AddMonoidHom.mulLeft (intMatrixEmb v HO))).relIndex L =
      (LinearMap.range (LinearMap.mulLeft (v.adicCompletionIntegers ℚ) HO)).toAddSubgroup.index := by
  have e_range : ∀ M, M ∈ L ↔ ∃ A, intMatrixEmb v A = M := fun M => by rw [hL, exists_intMatrixEmb_eq_iff]
  have hLtop : L = (⊤ : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ))).map
      (intMatrixEmb v).toAddMonoidHom := by
    ext M; rw [e_range]; constructor
    · rintro ⟨A, rfl⟩; exact ⟨A, trivial, rfl⟩
    · rintro ⟨A, -, rfl⟩; exact ⟨A, rfl⟩
  have hLH : L.map (AddMonoidHom.mulLeft (intMatrixEmb v HO)) =
      (LinearMap.range (LinearMap.mulLeft (v.adicCompletionIntegers ℚ) HO)).toAddSubgroup.map
        (intMatrixEmb v).toAddMonoidHom := by
    ext M
    constructor
    · rintro ⟨M', hM', rfl⟩
      obtain ⟨A, rfl⟩ := (e_range M').mp hM'
      refine ⟨HO * A, ⟨A, rfl⟩, ?_⟩
      show intMatrixEmb v (HO * A) = intMatrixEmb v HO * intMatrixEmb v A
      rw [map_mul]
    · rintro ⟨B, ⟨A, rfl⟩, rfl⟩
      refine ⟨intMatrixEmb v A, (e_range _).mpr ⟨A, rfl⟩, ?_⟩
      show intMatrixEmb v HO * intMatrixEmb v A = intMatrixEmb v (HO * A)
      rw [map_mul]
  rw [hLH, hLtop, AddSubgroup.relIndex_map_map_of_injective _ _ (intMatrixEmb_injective v),
    AddSubgroup.relIndex_top_right]

theorem index_range_mulLeft_map_ringEquiv {R R' S T : Type*} [CommRing R] [CommRing R'] [Ring S] [Ring T]
    [Algebra R S] [Algebra R' T] (ψ : S ≃+* T) (HO : S) :
    (LinearMap.range (LinearMap.mulLeft R HO)).toAddSubgroup.index =
      (LinearMap.range (LinearMap.mulLeft R' (ψ HO))).toAddSubgroup.index := by
  have h1 : (LinearMap.range (LinearMap.mulLeft R HO)).toAddSubgroup.map (ψ.toAddEquiv : S →+ T) =
      (LinearMap.range (LinearMap.mulLeft R' (ψ HO))).toAddSubgroup := by
    ext B
    constructor
    · rintro ⟨A', ⟨A, rfl⟩, rfl⟩
      refine ⟨ψ A, ?_⟩
      show ψ HO * ψ A = ψ (HO * A)
      rw [map_mul]
    · rintro ⟨B', rfl⟩
      refine ⟨HO * ψ.symm B', ⟨ψ.symm B', rfl⟩, ?_⟩
      show ψ (HO * ψ.symm B') = ψ HO * B'
      rw [map_mul, RingEquiv.apply_symm_apply]
  rw [← h1, AddSubgroup.index_map_equiv]

end IntModel

theorem relIndex_map_mulLeft_intMatrices_eq_sq_iff
    {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (L : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hL : ∀ M, M ∈ L ↔ ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ)
    (H K : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hH : H ∈ L) (hK : K ∈ L)
    (hHK : H * K = (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) :
    (L.map (AddMonoidHom.mulLeft H)).relIndex L = ℓ ^ 2 ↔
      ((algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • K ∉ L ∧
        (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • H ∉ L) := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hc : algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ) = (ℓ : v.adicCompletion ℚ) := map_natCast _ ℓ
  have hcinv : (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hℓ0, map_one]
  have hcinv' : (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) * (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = 1 := by
    rw [mul_comm]; exact hcinv

  have hHK1 : H * ((algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • K) = 1 := by
    rw [mul_smul_comm, hHK, smul_smul, hcinv, one_smul]
  have hKH1 : ((algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • K) * H = 1 := mul_eq_one_comm.mp hHK1
  have hKH : K * H = (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    have := congrArg (fun M => (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) • M) hKH1
    simpa only [smul_mul_assoc, smul_smul, hcinv', one_smul] using this
  have hKH1' : K * ((algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • H) = 1 := by
    rw [mul_smul_comm, hKH, smul_smul, hcinv, one_smul]
  have hHK1' : ((algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • H) * K = 1 := mul_eq_one_comm.mp hKH1'

  obtain ⟨HO, hHO⟩ := (exists_intMatrixEmb_eq_iff v H).mpr ((hL H).mp hH)
  obtain ⟨KO, hKO⟩ := (exists_intMatrixEmb_eq_iff v K).mpr ((hL K).mp hK)
  have hHOKO : HO * KO = (ℓ : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)) := by
    apply intMatrixEmb_injective v
    rw [map_mul, hHO, hKO, hHK, hc, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]

  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hpℓ : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = ℓ := by
    show Rat.HeightOneSpectrum.natGenerator v = ℓ
    have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ ℓ := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
      rwa [map_natCast] at this
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hdvd

  rw [← hHO, relIndex_map_mulLeft_eq_index v L hL HO,
    index_range_mulLeft_map_ringEquiv (R' := ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.mapMatrix HO,
    show ℓ ^ 2 = ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) ^ 2 from by rw [hpℓ]]
  have hψHK : (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.mapMatrix HO *
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.mapMatrix KO =
      (((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) •
        (1 : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) := by
    rw [← map_mul, hHOKO, map_natCast, ← hpℓ, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  have hC1 : (LinearMap.range (LinearMap.mulLeft ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]
      ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.mapMatrix HO))).toAddSubgroup.index =
        ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) ^ 2 ↔
      (¬ IsUnit ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.mapMatrix HO) ∧
        ¬ IsUnit ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv.mapMatrix KO)) := by
    rw [AddSubgroup.index_eq_card]
    exact natCard_quotient_range_mulLeft_eq_sq_iff ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) _ _ hψHK
  rw [hC1]
  rw [isUnit_map_ringEquiv_iff, isUnit_map_ringEquiv_iff,
    isUnit_iff_inverse_integral v HO _ (by rw [hHO]; exact hHK1) (by rw [hHO]; exact hKH1),
    isUnit_iff_inverse_integral v KO _ (by rw [hKO]; exact hKH1') (by rw [hKO]; exact hHK1'), ← hL, ← hL, hHO]

theorem relIndex_localBox_eq_sq_iff_of_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      z ∈ Submodule.localBox R v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (x h : (ℍ𝔸)ˣ)
    (h1 : (h : ℍ𝔸) ∈ Submodule.finiteAdeleBox R)
    (h2 : (ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R) :
    (Submodule.localBox (Submodule.ofFiniteIdele R (x * h)) v).relIndex
        (Submodule.localBox (Submodule.ofFiniteIdele R x) v) = ℓ ^ 2 ↔
      (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∉ Submodule.localBox R v ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ)⁻¹ • (h : ℍ𝔸)) ∉ Submodule.localBox R v) := by
  have hℓq : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  rw [relIndex_localBox_ofFiniteIdele_mul hR x h v]

  have hφinj : Function.Injective φ.toAddMonoidHom := φ.injective
  have hL : ∀ M, M ∈ (Submodule.localBox R v).map φ.toAddMonoidHom ↔
      ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ := by
    intro M
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact (hRv z).mp hz
    · intro hM
      refine ⟨φ.symm M, (hRv _).mpr ?_, ?_⟩
      · intro i j; rw [RingEquiv.apply_symm_apply]; exact hM i j
      · exact φ.apply_symm_apply M
  have hcomp : φ.toAddMonoidHom.comp (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸))) =
      (AddMonoidHom.mulLeft (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)))).comp φ.toAddMonoidHom := by
    refine AddMonoidHom.ext fun y => ?_
    show φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸) * y) =
      φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)) * φ y
    exact map_mul φ _ _
  rw [← AddSubgroup.relIndex_map_map_of_injective _ (Submodule.localBox R v) hφinj, AddSubgroup.map_map,
    hcomp, ← AddSubgroup.map_map]

  have hH : φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)) ∈ (Submodule.localBox R v).map φ.toAddMonoidHom :=
    ⟨_, finiteAdeleEvalAt_mem_localBox v h1, rfl⟩
  have hK : φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈
      (Submodule.localBox R v).map φ.toAddMonoidHom :=
    ⟨_, finiteAdeleEvalAt_mem_localBox v h2, rfl⟩
  have hprod : (h : ℍ𝔸) * ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) = (ℓ : ℚ) • (1 : ℍ𝔸) := by
    rw [mul_smul_comm, Units.mul_inv]
  have hHK : φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)) *
      φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) =
      (algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [← map_mul, ← map_mul, hprod, map_smul, map_one, ringEquiv_map_ratSmul v φ hφ, map_one]
  rw [relIndex_map_mulLeft_intMatrices_eq_sq_iff hℓ v hv _ hL _ _ hH hK hHK]

  have hinv : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (ℓ : ℚ)⁻¹ • ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [smul_smul, inv_mul_cancel₀ hℓq, one_smul]
  have e1 : (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) •
      φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) =
      φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    conv_rhs => rw [hinv, map_smul, ringEquiv_map_ratSmul v φ hφ]
  have e2 : (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) • φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : ℍ𝔸)) =
      φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ)⁻¹ • (h : ℍ𝔸))) := by
    rw [map_smul, ringEquiv_map_ratSmul v φ hφ]
  have memL : ∀ z, φ z ∈ (Submodule.localBox R v).map φ.toAddMonoidHom ↔ z ∈ Submodule.localBox R v :=
    fun z => by rw [hL, hRv]
  rw [e1, e2, memL, memL]

theorem mem_ofFiniteIdele_iff_inv_mul_mem (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) ∈ Submodule.finiteAdeleBox Λ := by

  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    rw [AddMonoidHom.coe_mulLeft] at hyz
    rw [← hyz, ← mul_assoc, Units.inv_mul, one_mul]
    exact hy
  · intro h
    exact ⟨_, h, by rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]⟩

theorem ofFiniteIdele_mul_le {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (x h : (ℍ𝔸)ˣ) (h1 : (h : ℍ𝔸) ∈ Submodule.finiteAdeleBox R) :
    Submodule.ofFiniteIdele R (x * h) ≤ Submodule.ofFiniteIdele R x := by
  intro z hz
  rw [mem_ofFiniteIdele_iff_inv_mul_mem] at hz ⊢
  have : ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) =
      (h : ℍ𝔸) * ((((x * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) := by
    rw [← mul_assoc, mul_inv_rev, Units.val_mul, ← mul_assoc (h : ℍ𝔸), Units.mul_inv, one_mul]
  rw [this]
  exact box_mul_mem hR h1 hz

theorem smul_mem_ofFiniteIdele_mul {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {ℓ : ℕ} (x h : (ℍ𝔸)ˣ) (h2 : (ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ Submodule.ofFiniteIdele R x) :
    (ℓ : ℚ) • z ∈ Submodule.ofFiniteIdele R (x * h) := by
  rw [mem_ofFiniteIdele_iff_inv_mul_mem] at hz ⊢
  have : (((x * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((ℓ : ℚ) • z) ⊗ₜ[ℚ] (1 : 𝔸f)) =
      ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) := by
    rw [mul_inv_rev, Units.val_mul, smul_mul_assoc, ← mul_smul_comm, ← mul_smul_comm, mul_assoc,
      TensorProduct.smul_tmul']
  rw [this]
  exact box_mul_mem hR h2 hz

theorem inv_mul_mem_box_of_le {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (x y : (ℍ𝔸)ˣ) (hle : Submodule.ofFiniteIdele R y ≤ Submodule.ofFiniteIdele R x) :
    (((x⁻¹ * y : (ℍ𝔸)ˣ)) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R := by
  have hy : (y : ℍ𝔸) ∈ Submodule.finiteAdeleBox (Submodule.ofFiniteIdele R y) := by
    rw [Submodule.finiteAdeleBox_ofFiniteIdele R hR.fg hR.spanTop y]
    exact ⟨1, one_mem_box hR, by simp⟩
  have hx := box_mono hle hy
  rw [Submodule.finiteAdeleBox_ofFiniteIdele R hR.fg hR.spanTop x] at hx
  obtain ⟨r, hr, hxr⟩ := hx
  rw [AddMonoidHom.coe_mulLeft] at hxr
  have : (((x⁻¹ * y : (ℍ𝔸)ˣ)) : ℍ𝔸) = r := by
    rw [Units.val_mul, ← hxr, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]; exact hr

theorem smul_inv_mem_box_of_forall_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {ℓ : ℕ} (x y : (ℍ𝔸)ˣ)
    (hℓ : ∀ z ∈ Submodule.ofFiniteIdele R x, (ℓ : ℚ) • z ∈ Submodule.ofFiniteIdele R y) :
    (ℓ : ℚ) • ((((x⁻¹ * y)⁻¹ : (ℍ𝔸)ˣ)) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R := by
  have hx : (x : ℍ𝔸) ∈ Submodule.finiteAdeleBox (Submodule.ofFiniteIdele R x) := by
    rw [Submodule.finiteAdeleBox_ofFiniteIdele R hR.fg hR.spanTop x]
    exact ⟨1, one_mem_box hR, by simp⟩
  have hle : (ℓ : ℚ) • Submodule.ofFiniteIdele R x ≤ Submodule.ofFiniteIdele R y := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w (ℓ : ℚ) _).mp hw
    exact hℓ z hz
  have h' := box_mono hle (box_smul_le (Submodule.ofFiniteIdele R x) (ℓ : ℚ) hx)
  rw [Submodule.finiteAdeleBox_ofFiniteIdele R hR.fg hR.spanTop y] at h'
  obtain ⟨r, hr, hyr⟩ := h'
  rw [AddMonoidHom.coe_mulLeft] at hyr
  have : (ℓ : ℚ) • ((((x⁻¹ * y)⁻¹ : (ℍ𝔸)ˣ)) : ℍ𝔸) = r := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, ← mul_smul_comm, ← hyr, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]; exact hr

theorem local_not_mem_of_mem_primeHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet R ℓ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∉ Submodule.localBox R v ∧
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ)⁻¹ • (h : ℍ𝔸)) ∉ Submodule.localBox R v := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hloc := Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop
  have haway : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := fun w hw =>
    inv_natCast_mem_adicCompletionIntegers hℓ.ne_zero w
      (fun hw' => hw (heightOneSpectrum_eq_of_natPrime_mem hℓ hw' hv))
  constructor
  · intro hc
    apply h3
    rw [hloc]
    intro w
    by_cases hw : w = v
    · subst hw; exact hc
    · have hu := map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ ⟨h1, h2, h3, h4⟩ w (haway w hw)
      exact hu.2
  · intro hc
    apply h4
    rw [hloc]
    intro w
    by_cases hw : w = v
    · subst hw; exact hc
    · have e : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((ℓ : ℚ)⁻¹ • (h : ℍ𝔸)) =
          ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) *
            Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (h : ℍ𝔸) := by
        rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def]
      rw [e]
      exact tmul_one_mul_mem_localBox w (haway w hw) (finiteAdeleEvalAt_mem_localBox w h1)

theorem not_mem_box_of_local_not_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {y : ℍ𝔸} (hy : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v y ∉ Submodule.localBox R v) :
    y ∉ Submodule.finiteAdeleBox R := fun hy' => hy (finiteAdeleEvalAt_mem_localBox v hy')

theorem relIndex_ofFiniteIdele_mul_eq_sq_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      z ∈ Submodule.localBox R v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (x h : (ℍ𝔸)ˣ)
    (h1 : (h : ℍ𝔸) ∈ Submodule.finiteAdeleBox R)
    (h2 : (ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R) :
    (Submodule.ofFiniteIdele R (x * h)).toAddSubgroup.relIndex
        (Submodule.ofFiniteIdele R x).toAddSubgroup = ℓ ^ 2 ↔
      (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∉ Submodule.localBox R v ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ℓ : ℚ)⁻¹ • (h : ℍ𝔸)) ∉ Submodule.localBox R v) := by
  have hL1 := isLattice_ofFiniteIdele hR x
  have hL2 := isLattice_ofFiniteIdele hR (x * h)
  rw [Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
      (Submodule.ofFiniteIdele R x) (Submodule.ofFiniteIdele R (x * h))
      hL1.fg Submodule.IsLattice.span_eq_top hL2.fg Submodule.IsLattice.span_eq_top
      (ofFiniteIdele_mul_le hR x h h1)]
  rw [finprod_eq_single _ v (fun w hw => relIndex_localBox_eq_one_of_not_mem hR hℓ.ne_zero x h h1 h2 w
      (fun hw' => hw (heightOneSpectrum_eq_of_natPrime_mem hℓ hw' hv)))]
  exact relIndex_localBox_eq_sq_iff_of_mem hR hℓ v hv φ hφ hRv x h h1 h2

end Ws43E7

open Ws43E7 in
theorem solution {a b : ℚ}
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      z ∈ Submodule.localBox R v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    (∃ h ∈ QuaternionAlgebra.primeHeckeSet R ℓ, J = Submodule.ofFiniteIdele R (x * h)) ↔
      (J ≤ Submodule.ofFiniteIdele R x ∧
        (∀ z ∈ Submodule.ofFiniteIdele R x, (ℓ : ℚ) • z ∈ J) ∧
        (∃ y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, J = Submodule.ofFiniteIdele R y) ∧
        J.toAddSubgroup.relIndex (Submodule.ofFiniteIdele R x).toAddSubgroup = ℓ ^ 2) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hh
    exact ⟨ofFiniteIdele_mul_le hR x h h1, fun z hz => smul_mem_ofFiniteIdele_mul hR x h h2 hz,
      ⟨x * h, rfl⟩,
      (relIndex_ofFiniteIdele_mul_eq_sq_iff hR hℓ v hv φ hφ hRv x h h1 h2).mpr
        (local_not_mem_of_mem_primeHeckeSet hR hℓ v hv ⟨h1, h2, h3, h4⟩)⟩
  · rintro ⟨hJ, hℓJ, ⟨y, rfl⟩, hidx⟩
    refine ⟨x⁻¹ * y, ?_, by rw [mul_inv_cancel_left]⟩
    have h1 := inv_mul_mem_box_of_le hR x y hJ
    have h2 := smul_inv_mem_box_of_forall_smul_mem hR x y hℓJ
    have key := (relIndex_ofFiniteIdele_mul_eq_sq_iff hR hℓ v hv φ hφ hRv x (x⁻¹ * y) h1 h2).mp
      (by rwa [mul_inv_cancel_left])
    exact ⟨h1, h2, not_mem_box_of_local_not_mem v key.1, not_mem_box_of_local_not_mem v key.2⟩

end S_QuaternionAlgebra_IsOrder_exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_mem_primeHeckeSet_eq_ofFiniteIdele_mul_iff (solution)
