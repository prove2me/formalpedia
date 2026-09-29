-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mulVec_mem_iff_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/55ed1b4f-a7c1-5f41-8ac5-f203fe4c0448

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_of_le
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

namespace P2mSteinitz

noncomputable def placeAt (r : ℕ) [hr : Fact r.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨r, hr.out⟩

theorem natCast_mem_placeAt (r : ℕ) [hr : Fact r.Prime] : ((r : ℕ) : 𝓞 ℚ) ∈ (placeAt r).asIdeal := by
  have h1 : Rat.HeightOneSpectrum.natGenerator (placeAt r) = r :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨r, hr.out⟩)
  have h2 := (Rat.HeightOneSpectrum.natGenerator_dvd_iff (placeAt r) (n := r)).mp (by rw [h1])
  rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) r, Ideal.apply_mem_of_equiv_iff] at h2
  exact h2

variable {A : Type*} [Ring A]

theorem fin_two_eq {a b c d a' b' c' d' : A} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c') (h₄ : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h₁ h₂ h₃ h₄; rfl

theorem diag_mulVec (a b : A) (y : Fin 2 → A) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) A).mulVec y = ![a * y 0, b * y 1] := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp

theorem diag_mul_diag (a b a' b' : A) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) A) * !![a', 0; 0, b'] = !![a * a', 0; 0, b * b'] := by
  rw [Matrix.mul_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

end P2mSteinitz

open P2mSteinitz in
theorem solution
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (I₁ I₂ : Submodule ℤ ℍ[ℚ, c, d])
    (h₁O : I₁ ≤ O) (h₁mul : ∀ z ∈ I₁, ∀ o ∈ O, z * o ∈ I₁) (h₁full : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I₁)
    (h₂O : I₂ ≤ O) (h₂mul : ∀ z ∈ I₂, ∀ o ∈ O, z * o ∈ I₂) (h₂full : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I₂) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → ℍ[ℚ, c, d],
        (∀ i, (γ'.mulVec x) i ∈ O) ↔ (x 0 ∈ I₁ ∧ x 1 ∈ I₂) := by
  classical

  obtain ⟨r, hr, hrq⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ q := by
    by_cases hq2 : q = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h => hq2 h.symm⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let v := placeAt r
  have hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := natCast_mem_placeAt r

  obtain ⟨β₁, g₁, hg₁, hd₁, hI₁⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem
      q hH O hO r hrq v hv I₁ h₁O h₁mul h₁full
  obtain ⟨β₂, g₂, hg₂, hd₂, hI₂⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_units_forall_mem_iff_mem_ofFiniteIdele_of_forall_mul_mem
      q hH O hO r hrq v hv I₂ h₂O h₂mul h₂full

  have hdet : ∀ φ : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ t : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, c, d]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) →
      (∀ x : ℍ[ℚ, c, d] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox O v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) →
      (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
          ((g₁ * g₂ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ ∧
      (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, c, d] v
          (((g₁ * g₂)⁻¹ : (ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, c, d] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))).det ∈ v.adicCompletionIntegers ℚ := by
    intro φ hφ1 hφO
    obtain ⟨a₁, b₁⟩ := hd₁ φ hφ1 hφO
    obtain ⟨a₂, b₂⟩ := hd₂ φ hφ1 hφO
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, map_mul, map_mul, Matrix.det_mul]
      exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem a₁ a₂
    · rw [mul_inv_rev, Units.val_mul, map_mul, map_mul, Matrix.det_mul]
      exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem b₂ b₁
  obtain ⟨γ₀, γ₀', h₀, h₀', hmem⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
      q hH O hO r hrq v hv g₁ g₂ hg₁ hg₂ hdet

  refine ⟨!![(β₁ : ℍ[ℚ, c, d]), 0; 0, (β₂ : ℍ[ℚ, c, d])] * γ₀,
    γ₀' * !![((β₁⁻¹ : (ℍ[ℚ, c, d])ˣ) : ℍ[ℚ, c, d]), 0; 0, ((β₂⁻¹ : (ℍ[ℚ, c, d])ˣ) : ℍ[ℚ, c, d])], ?_, ?_,
    fun x => ?_⟩
  · rw [mul_assoc, ← mul_assoc γ₀, h₀, one_mul, diag_mul_diag, Units.mul_inv, Units.mul_inv, Matrix.one_fin_two]
  · rw [mul_assoc, ← mul_assoc _ _ γ₀, diag_mul_diag, Units.inv_mul, Units.inv_mul, ← Matrix.one_fin_two, one_mul,
      h₀']
  · rw [← Matrix.mulVec_mulVec, diag_mulVec, hmem, hI₁, hI₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

end S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_of_le
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_of_le (solution)
