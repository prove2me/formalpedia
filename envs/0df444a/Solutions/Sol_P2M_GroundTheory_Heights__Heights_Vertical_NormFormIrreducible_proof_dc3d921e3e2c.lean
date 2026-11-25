-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_proof_dc3d921e3e2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:18:52.027434+00:00
-- url     : https://prove2.me/submissions/1a434476-eb74-4986-bc21-7c7b97f4e67f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_map_eq_prod_2f88ffb29b65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_prod_embForm_dvd_99f82f2e3334
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_embForm_6c2c91246726
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_map_algebraMap_57bf1cded0cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_exists_comp_eq_b7eb0fc85b9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_map_isUnit_782e4226fb8b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open NormFormIrreducible
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormFormIrreducible
theorem _root_.solution : NormFormIrreducible.Statement := by
  intro E L _ _ _ _ _ _ n x t hgen ht
  let _ : Field L := (isField_of_isIntegral_of_isField' (R := E) (Field.toIsField E)).toField
  classical
  let K := AlgebraicClosure E
  have hprod := normForm_map_eq_prod (E := E) (L := L) (K := K) x
  have hirr : ∀ σ : L →ₐ[E] K, Irreducible (embForm σ x) := fun σ => irreducible_embForm σ ht
  let σ₀ : L →ₐ[E] K := IsAlgClosed.lift
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun F G hFG => ?_⟩
  · have := hu.map (MvPolynomial.map (algebraMap E K))
    rw [hprod] at this
    exact (hirr σ₀).not_isUnit
      (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun σ => embForm σ x) (Finset.mem_univ σ₀)) this)
  · have hbar : ∏ σ : L →ₐ[E] K, embForm σ x =
        F.map (algebraMap E K) * G.map (algebraMap E K) := by
      rw [← hprod, hFG, map_mul]
    have hN0 : ∏ σ : L →ₐ[E] K, embForm σ x ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun σ _ => (hirr σ).ne_zero
    have hstable : ∀ p : MvPolynomial (Fin n) E, (∃ σ : L →ₐ[E] K, embForm σ x ∣ p.map (algebraMap E K)) →
        ∀ σ : L →ₐ[E] K, embForm σ x ∣ p.map (algebraMap E K) := by
      rintro p ⟨σ, hσ⟩ σ'
      obtain ⟨τ, rfl⟩ := exists_comp_eq σ σ'
      have := map_dvd (MvPolynomial.map (τ : K →+* K)) hσ
      rwa [map_embForm, map_map_algebraMap] at this
    have hunit : ∀ P Q : MvPolynomial (Fin n) E, (∀ σ : L →ₐ[E] K, embForm σ x ∣ P.map (algebraMap E K)) →
        ∏ σ : L →ₐ[E] K, embForm σ x = P.map (algebraMap E K) * Q.map (algebraMap E K) →
          IsUnit Q := by
      intro P Q hP hPQ
      have hd := prod_embForm_dvd hgen ht hP
      rw [hPQ] at hd hN0
      have hP0 : P.map (algebraMap E K) ≠ 0 := left_ne_zero_of_mul hN0
      conv_rhs at hd => rw [← mul_one (P.map (algebraMap E K))]
      exact isUnit_of_map_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hP0).mp hd))
    by_cases hF : ∃ σ : L →ₐ[E] K, embForm σ x ∣ F.map (algebraMap E K)
    · exact Or.inr (hunit F G (hstable F hF) hbar)
    · simp only [not_exists] at hF
      refine Or.inl (hunit G F (hstable G ⟨σ₀, ?_⟩) (by rw [hbar, mul_comm]))
      exact ((hirr σ₀).prime.dvd_or_dvd
        (hbar ▸ Finset.dvd_prod_of_mem (fun σ => embForm σ x) (Finset.mem_univ σ₀))).resolve_left (hF σ₀)
end NormFormIrreducible
end GroundTheory.Heights₂.Heights.Vertical
