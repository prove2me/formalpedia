-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2f81e029-7173-5238-b51a-6fbe2c614d2d

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace EichlerLocalModel

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem valued_natCast_eq_one {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v (n : v.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := v)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_notMem {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one v hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one v hn, inv_one]

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (v : HeightOneSpectrum (𝓞 ℚ))

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem localBox_le_of_nsmul_mem {Λ Λ' : Submodule ℤ D} {N : ℕ} (hN : (N : 𝓞 ℚ) ∉ v.asIdeal)
    (h : ∀ z ∈ Λ', (N : ℤ) • z ∈ Λ) :
    Submodule.localBox Λ' v ≤ Submodule.localBox Λ v := by
  unfold Submodule.localBox
  rw [AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have hN0 := natCast_ne_zero_of_notMem v hN
  have : z ⊗ₜ[ℚ] c = ((N : ℤ) • z) ⊗ₜ[ℚ] ((N : v.adicCompletion ℚ)⁻¹ * c) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Int.cast_natCast, Algebra.smul_def,
      map_natCast, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  rw [this]
  exact AddSubgroup.subset_closure ⟨(N : ℤ) • z, h z hz, _, mul_mem (natCast_inv_mem_integers v hN) hc, rfl⟩

end Box

section Split

variable {a b : ℚ} {q' : ℕ} (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
  (v : HeightOneSpectrum (𝓞 ℚ)) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

include hB hq'v in

theorem exists_split : ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] 𝕂 ≃+* M₂,
    ∀ r : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : M₂) := by

  have hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] 𝕂, x ≠ 0 → IsUnit x := by
    rw [hB.2.2 v]
    exact hq'v
  push Not at hnd
  obtain ⟨x, hx0, hxu⟩ := hnd

  obtain ⟨φ₀, hφ₀1, hφ₀x⟩ :=
    QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
      (R := ℚ) (S := 𝕂) (T := ℍ[𝕂, algebraMap ℚ 𝕂 a, 0, algebraMap ℚ 𝕂 b]) (c₁ := a) (c₂ := (0 : ℚ))
      (c₃ := b) rfl (map_zero _) rfl AlgEquiv.refl
  have hx0' : φ₀ x ≠ 0 := fun h => hx0 (by simpa using congrArg φ₀.symm h)
  have hxu' : ¬ IsUnit (φ₀ x) := fun h => hxu (by simpa using h.map φ₀.symm)
  haveI : CharZero 𝕂 := charZero_of_injective_algebraMap (algebraMap ℚ 𝕂).injective
  haveI : NeZero (2 : 𝕂) := ⟨two_ne_zero⟩
  have ha : algebraMap ℚ 𝕂 a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ 𝕂).injective]; exact hB.1.ne
  have hb : algebraMap ℚ 𝕂 b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ 𝕂).injective]; exact hB.2.1.ne
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit ha hb (φ₀ x) hx0' hxu'
  obtain ⟨φ, hφ1, -⟩ :=
    QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
      (R := ℚ) (S := 𝕂) (T := M₂) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) rfl (map_zero _) rfl ψ
  exact ⟨φ, hφ1⟩

end Split

section Conj

variable {K : Type*} [Field K] (h : GL (Fin 2) K)

def conjEquiv : Matrix (Fin 2) (Fin 2) K ≃+* Matrix (Fin 2) (Fin 2) K where
  toFun x := ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (h : Matrix (Fin 2) (Fin 2) K)
  invFun x := (h : Matrix (Fin 2) (Fin 2) K) * x * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  left_inv x := by
    have e : (h : Matrix (Fin 2) (Fin 2) K) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
      Units.mul_inv h
    show (h : Matrix (Fin 2) (Fin 2) K) * (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x *
      (h : Matrix (Fin 2) (Fin 2) K)) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = x
    calc _ = ((h : Matrix (Fin 2) (Fin 2) K) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * x *
          ((h : Matrix (Fin 2) (Fin 2) K) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
            noncomm_ring
      _ = x := by rw [e, one_mul, mul_one]
  right_inv x := by
    have e : ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) = 1 :=
      Units.inv_mul h
    show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((h : Matrix (Fin 2) (Fin 2) K) * x *
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * (h : Matrix (Fin 2) (Fin 2) K) = x
    calc _ = (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) * x *
          (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) := by
            noncomm_ring
      _ = x := by rw [e, one_mul, mul_one]
  map_mul' x y := by
    have e : (h : Matrix (Fin 2) (Fin 2) K) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
      Units.mul_inv h
    show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x * y) * (h : Matrix (Fin 2) (Fin 2) K) =
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (h : Matrix (Fin 2) (Fin 2) K) *
        (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * y * (h : Matrix (Fin 2) (Fin 2) K))
    calc _ = ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x *
          ((h : Matrix (Fin 2) (Fin 2) K) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * y *
          (h : Matrix (Fin 2) (Fin 2) K) := by rw [e]; noncomm_ring
      _ = _ := by noncomm_ring
  map_add' x y := by
    show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x + y) * (h : Matrix (Fin 2) (Fin 2) K) = _
    rw [mul_add, add_mul]

theorem conjEquiv_apply (x : Matrix (Fin 2) (Fin 2) K) :
    conjEquiv h x = ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (h : Matrix (Fin 2) (Fin 2) K) :=
  rfl

end Conj

theorem main {a b : ℚ} {q' : ℕ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal) (hNv : (N : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ := by

  obtain ⟨Λ₁, hΛ₁, hRΛ₁, hidx⟩ := hR.exists_le_isMaximalOrder
  have hNΛ₁ : ∀ z ∈ Λ₁, (N : ℤ) • z ∈ R := by
    intro z hz
    have h := AddSubgroup.nsmul_relIndex_mem R.toAddSubgroup (K := Λ₁.toAddSubgroup) (g := z) hz
    rw [hidx] at h
    have : (N : ℤ) • z = N • z := by rw [natCast_zsmul]
    rw [this]
    exact h
  have hbox : Submodule.localBox R v = Submodule.localBox Λ₁ v :=
    le_antisymm (localBox_mono v hRΛ₁) (localBox_le_of_nsmul_mem v hNv hNΛ₁)

  obtain ⟨φ₀, hφ₀⟩ := exists_split hdef v hq'v
  obtain ⟨h, hh⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
      hΛ₁ v φ₀ hφ₀
  refine ⟨φ₀.trans (conjEquiv h), fun r => ?_, fun x => ?_⟩
  · rw [RingEquiv.trans_apply, conjEquiv_apply, hφ₀, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    rw [show ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 from Units.inv_mul h]
  · rw [hbox, hh x]
    rfl

end EichlerLocalModel

theorem solution
    {a b : ℚ} {q' : ℕ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal) (hNv : (N : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ :=
  EichlerLocalModel.main hdef hR v hq'v hNv

end

end S_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem (solution)
