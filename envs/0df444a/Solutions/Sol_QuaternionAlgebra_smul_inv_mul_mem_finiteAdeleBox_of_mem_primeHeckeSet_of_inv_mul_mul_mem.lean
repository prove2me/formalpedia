-- Prove2me | solution 1 for QuaternionAlgebra.smul_inv_mul_mem_finiteAdeleBox_of_mem_primeHeckeSet_of_inv_mul_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/98eb2d4a-65ef-59e7-8bd8-a23e83fd2955

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_smul_inv_mul_mem_finiteAdeleBox_of_mem_primeHeckeSet_of_inv_mul_mul_mem
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace QSandwichC2b

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Places

theorem valued_natCast_eq_one {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_notMem {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one w hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

theorem natCast_mem_integers (w : HOS) (n : ℕ) : (n : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = _ at h
  rw [map_natCast] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact HeightOneSpectrum.valuation_le_one w _

theorem intCast_mem_integers (w : HOS) (n : ℤ) : (n : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = _ at h
  rw [map_intCast] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact HeightOneSpectrum.valuation_le_one w _

theorem natCast_notMem_of_coprime {ℓ : ℕ} (v : HOS) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (n : ℕ)
    (hn : Nat.Coprime ℓ n) : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hnP
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hn
  have : (1 : 𝓞 ℚ) = (u : 𝓞 ℚ) * (ℓ : 𝓞 ℚ) + (w : 𝓞 ℚ) * (n : 𝓞 ℚ) := by
    have := congrArg (Int.cast : ℤ → 𝓞 ℚ) huw
    push_cast at this
    exact this.symm
  rw [this]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hℓv) (v.asIdeal.mul_mem_left _ hnP)

end Places

section LocalBox

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem tmul_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) {c : w.adicCompletion ℚ}
    (hc : c ∈ w.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_mem_localBox {Λ : Submodule ℤ D} (h1 : (1 : D) ∈ Λ) (w : HOS) :
    (1 : D ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_localBox h1 w (one_mem _)

theorem gen_mul_mem_localBox (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (w : HOS)
    {z : D} (hz : z ∈ Λ) {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ)
    {y : D ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) :
    (z ⊗ₜ[ℚ] c) * y ∈ Submodule.localBox Λ w := by
  unfold Submodule.localBox at hy ⊢
  refine AddSubgroup.closure_induction (p := fun y _ => (z ⊗ₜ[ℚ] c) * y ∈ _) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hmul z z' hz hz', c * c', mul_mem hc hc', rfl⟩
  · show z ⊗ₜ[ℚ] c * 0 ∈ _
    rw [mul_zero]; exact AddSubgroup.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]; exact AddSubgroup.add_mem _ hx hy
  · intro x _ hx
    convert AddSubgroup.neg_mem _ hx using 1
    exact mul_neg (z ⊗ₜ[ℚ] c) x

theorem localBox_mul_mem (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (w : HOS)
    {x y : D ⊗[ℚ] w.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ w) (hy : y ∈ Submodule.localBox Λ w) :
    x * y ∈ Submodule.localBox Λ w := by
  have hy' := hy
  unfold Submodule.localBox at hx
  refine AddSubgroup.closure_induction (p := fun x _ => x * y ∈ Submodule.localBox Λ w) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, hz, c, hc, rfl⟩
    exact gen_mul_mem_localBox Λ hmul w hz hc hy'
  · show 0 * y ∈ _
    rw [zero_mul]; exact AddSubgroup.zero_mem _
  · intro x₁ x₂ _ _ h₁ h₂
    rw [add_mul]; exact AddSubgroup.add_mem _ h₁ h₂
  · intro x₁ _ h₁
    convert AddSubgroup.neg_mem _ h₁ using 1
    exact neg_mul x₁ y

theorem rat_smul_eq_one_tmul_mul (w : HOS) (q : ℚ) (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    q • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) q)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z s =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem one_tmul_mul_comm (w : HOS) (r : w.adicCompletion ℚ) (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    ((1 : D) ⊗ₜ[ℚ] r) * x = x * ((1 : D) ⊗ₜ[ℚ] r) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z s =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm r s]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

theorem one_tmul_inv_mul_one_tmul_mul (w : HOS) {c : w.adicCompletion ℚ} (hc : c ≠ 0)
    (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    ((1 : D) ⊗ₜ[ℚ] c⁻¹) * (((1 : D) ⊗ₜ[ℚ] c) * x) = x := by
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hc,
    ← Algebra.TensorProduct.one_def, one_mul]

end LocalBox

section Quaternion

open QuaternionAlgebra

variable {a b : ℚ} (v : HOS)

theorem trd_add' {K : Type*} [CommRing K] {α β : K} (x y : ℍ[K, α, β]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, trd_mk]; ring

theorem trd_neg' {K : Type*} [CommRing K] {α β : K} (x : ℍ[K, α, β]) : trd (-x) = -trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.neg_mk, trd_mk]; ring

theorem trd_zero' {K : Type*} [CommRing K] {α β : K} : trd (0 : ℍ[K, α, β]) = 0 := by
  simp [trd]

theorem trd_smul' {K : Type*} [CommRing K] {α β : K} (c : K) (x : ℍ[K, α, β]) : trd (c • x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, trd_mk, smul_eq_mul]; ring

theorem coe_eq_smul_one {K : Type*} [CommRing K] {α β : K} (r : K) :
    ((r : K) : ℍ[K, α, β]) = r • (1 : ℍ[K, α, β]) := by
  rw [← mul_one ((r : K) : ℍ[K, α, β]), coe_mul_eq_smul]

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ) ≃+* ℍ[(v.adicCompletion ℚ), algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ₁ : ∀ r : (v.adicCompletion ℚ), φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : ℍ[(v.adicCompletion ℚ), algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : (v.adicCompletion ℚ)),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ : ℍ[(v.adicCompletion ℚ), algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hφ in
theorem trd_φ_tmul (z : ℍ[ℚ, a, b]) (c : (v.adicCompletion ℚ)) :
    trd (φ (z ⊗ₜ[ℚ] c)) = c * algebraMap ℚ (v.adicCompletion ℚ) (trd z) := by
  rw [hφ, trd_smul']
  congr 1
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [trd_mk, map_mul, map_ofNat]

include hφ in

theorem trd_mem_of_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ)} (hx : x ∈ Submodule.localBox Λ v) :
    trd (φ x) ∈ v.adicCompletionIntegers ℚ := by
  unfold Submodule.localBox at hx
  refine AddSubgroup.closure_induction (p := fun x _ => trd (φ x) ∈ v.adicCompletionIntegers ℚ)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, hz, c, hc, rfl⟩
    obtain ⟨-, t, ht⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hz
    rw [trd_φ_tmul v φ hφ, ← ht, map_intCast]
    exact mul_mem hc (intCast_mem_integers v t)
  · show trd (φ 0) ∈ _
    rw [map_zero, trd_zero']; exact zero_mem _
  · intro x y _ _ hx hy
    show trd (φ (x + y)) ∈ _
    rw [map_add, trd_add']; exact add_mem hx hy
  · intro x _ hx
    show trd (φ (-x)) ∈ _
    rw [map_neg, trd_neg']; exact neg_mem hx

include hφ₁ in

theorem φ_one_tmul_mul (r : (v.adicCompletion ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ)) : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) * x) = r • φ x := by
  rw [map_mul, hφ₁, smul_mul_assoc, one_mul]

include hφ₁ hφ in

theorem conj_inv_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u u' m m' : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ)} (huu' : u * u' = 1) (hu'u : u' * u = 1) (hm'm : m' * m = 1)
    (hu' : u' ∈ Submodule.localBox Λ v) (hy : m' * u * m ∈ Submodule.localBox Λ v) :
    m' * u' * m ∈ Submodule.localBox Λ v := by
  have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun x y hx hy => hΛ.mul_mem hx hy

  set t' : (v.adicCompletion ℚ) := trd (φ u') with ht'_def
  have ht' : t' ∈ v.adicCompletionIntegers ℚ := trd_mem_of_mem_localBox v φ hφ hΛ hu'
  have h1t' : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') ∈ Submodule.localBox Λ v := tmul_mem_localBox hΛ.one_mem v ht'

  set s : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ) := ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') - u' with hs_def
  have hs : s ∈ Submodule.localBox Λ v := sub_mem h1t' hu'
  have hφs : φ s = star (φ u') := by
    rw [hs_def, map_sub, hφ₁, ← coe_eq_smul_one, sub_eq_iff_eq_add, add_comm, add_star_eq_coe_trd, ht'_def]
  set c : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ) := u' * s with hc_def
  have hc : c ∈ Submodule.localBox Λ v := localBox_mul_mem Λ hmul v hu' hs
  have hc' : c = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (nrd (φ u')) := by
    apply φ.injective
    rw [hc_def, map_mul, hφs, mul_star_eq_coe_nrd, hφ₁, coe_eq_smul_one]

  have hid : u' = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') - c * u := by
    have : c * u = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') - u' := by
      rw [hc_def, hs_def, mul_sub, sub_mul, mul_assoc u' ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') u,
        one_tmul_mul_comm v t' u, ← mul_assoc u' u _, hu'u, one_mul, mul_assoc u' u' u, hu'u, mul_one]
    rw [this, sub_sub_cancel]

  have hconj : m' * u' * m = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') - c * (m' * u * m) := by
    conv_lhs => rw [hid]
    rw [mul_sub, sub_mul, ← one_tmul_mul_comm v t' m', mul_assoc ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t') m' m, hm'm,
      mul_one, hc', ← mul_assoc m' ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (nrd (φ u'))) u, ← one_tmul_mul_comm v _ m']
    simp only [mul_assoc]
  rw [hconj]
  refine sub_mem h1t' ?_
  exact localBox_mul_mem Λ hmul v hc hy

theorem conj_inv_mem_localBox' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u u' m m' : ℍ[ℚ, a, b] ⊗[ℚ] (v.adicCompletion ℚ)} (huu' : u * u' = 1) (hu'u : u' * u = 1) (hm'm : m' * m = 1)
    (hu' : u' ∈ Submodule.localBox Λ v) (hy : m' * u * m ∈ Submodule.localBox Λ v) :
    m' * u' * m ∈ Submodule.localBox Λ v := by
  obtain ⟨φ, hφ₁, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := (v.adicCompletion ℚ)) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (v.adicCompletion ℚ) a) (d₂ := (0 : (v.adicCompletion ℚ))) (d₃ := algebraMap ℚ (v.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : (v.adicCompletion ℚ)),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ : ℍ[(v.adicCompletion ℚ), algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) :=
    fun z r => by rw [hφ]; simp only [AlgEquiv.coe_refl, id_eq]
  exact conj_inv_mem_localBox v φ hφ₁ hφ' hΛ huu' hu'u hm'm hu' hy

end Quaternion

end QSandwichC2b

end

open QSandwichC2b in
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve in
theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N)
    (n₀ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₀ : n₀ ∈ primeHeckeSet Λ₁ q)
    (hmm' : ((m⁻¹ * (n₀ * m) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁) :
    ((q : ℕ) : ℚ) • (((n₀ * m)⁻¹ * m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ := by
  have hord : QuaternionAlgebra.IsOrder Λ₁ := hΛ₁.1
  have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ₁ → y ∈ Λ₁ → x * y ∈ Λ₁ := fun x y hx hy => hord.mul_mem hx hy
  have hq : q.Prime := Fact.out
  have hbox := fun t => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
    (D := ℍ[ℚ, a, b]) Λ₁ hord.fg hord.spanTop t
  rw [hbox]
  intro v

  set E := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hE
  set mv := E (m : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) with hmv
  set mv' := E ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) with hmv'
  set nv := E (n₀ : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) with hnv
  set nv' := E ((n₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) with hnv'
  have hmm'v : mv * mv' = 1 := by rw [hmv, hmv', ← map_mul, Units.mul_inv, map_one]
  have hm'mv : mv' * mv = 1 := by rw [hmv, hmv', ← map_mul, Units.inv_mul, map_one]
  have hnn'v : nv * nv' = 1 := by rw [hnv, hnv', ← map_mul, Units.mul_inv, map_one]
  have hn'nv : nv' * nv = 1 := by rw [hnv, hnv', ← map_mul, Units.inv_mul, map_one]

  have h1 : mv ∈ Submodule.localBox Λ₁ v := (hbox _).mp hm₁ v
  have h2 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : v.adicCompletion ℚ)) * mv' ∈ Submodule.localBox Λ₁ v := by
    have := (hbox _).mp hmN v
    rwa [map_smul, rat_smul_eq_one_tmul_mul, map_natCast] at this
  have h3 : nv ∈ Submodule.localBox Λ₁ v := (hbox _).mp hn₀.1 v
  have h4 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : v.adicCompletion ℚ)) * nv' ∈ Submodule.localBox Λ₁ v := by
    have := (hbox _).mp hn₀.2.1 v
    rwa [map_smul, rat_smul_eq_one_tmul_mul, map_natCast] at this
  have h5 : mv' * nv * mv ∈ Submodule.localBox Λ₁ v := by
    have := (hbox _).mp hmm' v
    rwa [Units.val_mul, Units.val_mul, map_mul, map_mul, ← mul_assoc] at this

  rw [map_smul, rat_smul_eq_one_tmul_mul, map_natCast, mul_inv_rev, Units.val_mul, Units.val_mul, map_mul,
    map_mul]
  change ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : v.adicCompletion ℚ)) * (mv' * nv' * mv) ∈ Submodule.localBox Λ₁ v
  by_cases hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  ·
    have hNv : ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
      natCast_notMem_of_coprime v hqv N ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN)
    have hmv'mem : mv' ∈ Submodule.localBox Λ₁ v := by
      have := gen_mul_mem_localBox Λ₁ hmul v hord.one_mem (natCast_inv_mem_integers v hNv) h2
      rwa [one_tmul_inv_mul_one_tmul_mul v (natCast_ne_zero_of_notMem v hNv)] at this
    have hre : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : v.adicCompletion ℚ)) * (mv' * nv' * mv) =
        mv' * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : v.adicCompletion ℚ)) * nv') * mv := by
      simp only [← mul_assoc, (one_tmul_mul_comm v ((q : ℕ) : v.adicCompletion ℚ) mv').symm]
    rw [hre]
    exact localBox_mul_mem Λ₁ hmul v (localBox_mul_mem Λ₁ hmul v hmv'mem h4) h1
  ·
    have hnv'mem : nv' ∈ Submodule.localBox Λ₁ v := by
      have := gen_mul_mem_localBox Λ₁ hmul v hord.one_mem (natCast_inv_mem_integers v hqv) h4
      rwa [one_tmul_inv_mul_one_tmul_mul v (natCast_ne_zero_of_notMem v hqv)] at this
    have hkey : mv' * nv' * mv ∈ Submodule.localBox Λ₁ v :=
      conj_inv_mem_localBox' v hord hnn'v hn'nv hm'mv hnv'mem h5
    exact gen_mul_mem_localBox Λ₁ hmul v hord.one_mem (natCast_mem_integers v q) hkey

end S_QuaternionAlgebra_smul_inv_mul_mem_finiteAdeleBox_of_mem_primeHeckeSet_of_inv_mul_mul_mem
end P2MW
export P2MW.S_QuaternionAlgebra_smul_inv_mul_mem_finiteAdeleBox_of_mem_primeHeckeSet_of_inv_mul_mul_mem (solution)
