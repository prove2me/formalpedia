-- Prove2me | solution 1 for QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3ae10bcb-e468-5d4d-bcb9-ba3b5a4e9a3c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute
import Theorems.Thm_QuaternionAlgebra_exists_mul_mul_eq_one_and_forall_apply_mem_of_algHom_matrix_injective_of_isOrder_of_isMaximalOrder
import Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos
import Theorems.Thm_QuaternionAlgebra_exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg
import Theorems.Thm_QuaternionAlgebra_exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace P2mQuatEmbed

variable {c d : ℚ}

def conjAlgHom (γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (h : γ * γ' = 1) (h' : γ' * γ = 1) : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] where
  toFun y := γ' * y * γ
  map_one' := by rw [mul_one, h']
  map_mul' a b := by
    calc γ' * (a * b) * γ = γ' * a * (γ * γ') * b * γ := by rw [h]; simp only [mul_one, mul_assoc]
      _ = γ' * a * γ * (γ' * b * γ) := by simp only [mul_assoc]
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' a b := by rw [mul_add, add_mul]
  commutes' q := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, h']

@[scoped simp] theorem conjAlgHom_apply (γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (h : γ * γ' = 1) (h' : γ' * γ = 1) (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) :
    conjAlgHom γ γ' h h' y = γ' * y * γ := rfl

theorem conjAlgHom_injective (γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (h : γ * γ' = 1) (h' : γ' * γ = 1) :
    Function.Injective (conjAlgHom γ γ' h h') := by
  intro a b hab
  simp only [conjAlgHom_apply] at hab
  have : γ * (γ' * a * γ) * γ' = γ * (γ' * b * γ) * γ' := by rw [hab]
  simpa only [mul_assoc, h, ← mul_assoc γ γ', one_mul, mul_one] using this

theorem commute_combo {X W Y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]} (hX : Y * X = X * Y) (hW : Y * W = W * Y) (α β γ δ : ℚ) :
    Y * (α • 1 + β • X + γ • W + δ • (X * W)) = (α • 1 + β • X + γ • W + δ • (X * W)) * Y := by
  have hXW : Y * (X * W) = X * W * Y := by rw [← mul_assoc, hX, mul_assoc, hW, mul_assoc]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hX, hW, hXW]

end P2mQuatEmbed
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt.P2mQuatEmbed"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt.P2mQuatEmbed"

open P2mQuatEmbed in

theorem solution
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar) :
    ∃ (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
      (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O),
      Function.Injective j ∧ Function.Injective τ ∧
      (∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ) ∧
      ∀ (F : Type) [Field F] [CharP F r] (χ : ↥O → F),
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
        (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F) := by
  classical

  have hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x :=
    fun v hv => (hB.2 v).mpr (Or.inl hv)

  obtain ⟨t, s, x, w, y, ρ, ht, hs, hx, hw, hxw, hspanB, hy, hρ, hρx, hρw⟩ :=
    QuaternionAlgebra.exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos
      r hH' hBq hB.1

  obtain ⟨z, c', hc', hz, hyz, hspanH⟩ :=
    QuaternionAlgebra.exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg
      hH'.1 hH'.2.1 y t ht hy

  obtain ⟨eB, -, -⟩ := QuaternionAlgebra.exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
    t s ht.ne hs.ne' x w hx hw hxw hspanB
  obtain ⟨eH, -, -⟩ := QuaternionAlgebra.exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
    t c' ht.ne hc'.ne y z hy hz hyz hspanH
  have hBts : IsIndefiniteRamifiedExactlyAt t s r rbar :=
    ⟨Or.inr hs, fun v => (QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv eB v).trans (hB.2 v)⟩
  have hHtc : IsDefiniteRamifiedExactlyAt t c' r :=
    ⟨ht, hc', fun v => (QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv eH v).trans (hH'.2.2 v)⟩

  have hC : IsDefiniteRamifiedExactlyAt t (s * c') rbar :=
    QuaternionAlgebra.isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt hrr hBts hHtc
  obtain ⟨φ⟩ := QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt hdef hC

  obtain ⟨τ₀, hτ₀, -, -, hcomm⟩ :=
    QuaternionAlgebra.exists_algHom_matrix_forall_commute_iff_mem_range_of_mul_self_of_anticommute
      t s c' ht.ne hs.ne' hc'.ne y z hy hz hyz hspanH

  obtain ⟨γ, γ', hγ, hγ', hint⟩ :=
    QuaternionAlgebra.exists_mul_mul_eq_one_and_forall_apply_mem_of_algHom_matrix_injective_of_isOrder_of_isMaximalOrder
      r hH' hBq Λ hΛ.isOrder O hO ρ hρ
  let j₀ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] := (conjAlgHom γ γ' hγ hγ').comp ρ
  have hj₀ : ∀ m ∈ Λ, ∀ i l : Fin 2, j₀ m i l ∈ O := fun m hm i l => hint m hm i l
  obtain ⟨j, δ, δ', hδ, hδ', hjconj, hj, htrace⟩ :=
    QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
      hB Λ hΛ hH' O hO j₀ hj₀

  set P : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] := γ * δ with hPdef
  set P' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] := δ' * γ' with hP'def
  clear_value P P'
  have hP : P * P' = 1 := by rw [hPdef, hP'def, mul_assoc, ← mul_assoc δ, hδ, one_mul, hγ]
  have hP' : P' * P = 1 := by rw [hPdef, hP'def, mul_assoc, ← mul_assoc γ', hγ', one_mul, hδ']
  have hjP : ∀ m : ℍ[ℚ, a, b], j m = P' * ρ m * P := by
    intro m; rw [hjconj m]; simp only [j₀, AlgHom.comp_apply, conjAlgHom_apply, hPdef, hP'def, mul_assoc]
  have hρP : ∀ m : ℍ[ℚ, a, b], ρ m = P * j m * P' := by
    intro m
    rw [hjP m]
    simp only [← mul_assoc]
    rw [hP, one_mul, mul_assoc, hP, mul_one]

  let τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d] := ((conjAlgHom P P' hP hP').comp τ₀).comp (φ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] ℍ[ℚ, t, s * c'])
  have hτ_apply : ∀ h : ℍ[ℚ, a₁, b₁], τ h = P' * τ₀ (φ h) * P := fun h => rfl
  refine ⟨j, τ, hj, ?_, ?_, ?_, htrace⟩
  ·
    intro m₁ m₂ hm
    apply hρ
    rw [hρP m₁, hρP m₂, hm]
  ·
    exact ((conjAlgHom_injective P P' hP hP').comp hτ₀).comp φ.injective
  ·
    intro Y
    constructor
    · intro hY

      have hY' : ∀ m : ℍ[ℚ, a, b], (P * Y * P') * ρ m = ρ m * (P * Y * P') := by
        intro m
        rw [hρP m]
        calc P * Y * P' * (P * j m * P') = P * (Y * j m) * P' := by
              simp only [mul_assoc]; rw [← mul_assoc P' P, hP', one_mul]
          _ = P * (j m * Y) * P' := by rw [hY m]
          _ = P * j m * P' * (P * Y * P') := by
              simp only [mul_assoc]; rw [← mul_assoc P' P, hP', one_mul]
      have hX := hY' x
      have hW := hY' w
      rw [hρx] at hX; rw [hρw] at hW
      obtain ⟨h₀, hh₀⟩ := (hcomm (P * Y * P')).mp ⟨hX, hW⟩
      refine ⟨φ.symm h₀, ?_⟩
      rw [hτ_apply, AlgEquiv.apply_symm_apply, hh₀]
      simp only [mul_assoc]
      rw [← mul_assoc P' P, hP', one_mul, mul_one]
    · rintro ⟨h, rfl⟩
      intro m
      have hmem : τ₀ (φ h) ∈ Set.range τ₀ := ⟨φ h, rfl⟩
      obtain ⟨hX, hW⟩ := (hcomm (τ₀ (φ h))).mpr hmem
      rw [← hρx] at hX; rw [← hρw] at hW

      obtain ⟨α, β, γ₁, δ₁, hm⟩ := hspanB m
      have hcm : τ₀ (φ h) * ρ m = ρ m * τ₀ (φ h) := by
        rw [hm, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_one, map_mul]
        exact commute_combo hX hW α β γ₁ δ₁
      rw [hτ_apply, hjP m]
      calc P' * τ₀ (φ h) * P * (P' * ρ m * P) = P' * (τ₀ (φ h) * ρ m) * P := by
            simp only [mul_assoc]; rw [← mul_assoc P P', hP, one_mul]
        _ = P' * (ρ m * τ₀ (φ h)) * P := by rw [hcm]
        _ = P' * ρ m * P * (P' * τ₀ (φ h) * P) := by
            simp only [mul_assoc]; rw [← mul_assoc P P', hP, one_mul]

end S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt (solution)
