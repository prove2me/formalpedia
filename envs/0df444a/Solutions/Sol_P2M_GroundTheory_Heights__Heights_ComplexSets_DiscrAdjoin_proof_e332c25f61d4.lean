-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_DiscrAdjoin_proof_e332c25f61d4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:56.49934+00:00
-- url     : https://prove2.me/submissions/560dfa4b-840d-4870-99d2-13135668a986

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscrAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace DiscrAdjoin
theorem _root_.solution : DiscrAdjoin.Statement := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj
  have hK : IsIntegral K ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ
  have hFm : (minpoly R ℓ).Monic := minpoly.monic hℓ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree := by
    rw [hFK, natDegree_map_eq_of_injective hinj]
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    have h1 := IntermediateField.adjoin.finrank hK
    rw [hadj, IntermediateField.finrank_top', hdegK] at h1
    exact h1.symm
  have hpos : 0 < (minpoly R ℓ).natDegree := minpoly.natDegree_pos hℓ
  have hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1 :=
    natDegree_derivative_le _
  have hres := resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)
  rw [hFm.leadingCoeff, mul_one] at hres
  have hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree *
      ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ))
        (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) := by
    rw [hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hdeg, ?_, ?_⟩
  · intro h0
    have hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree
        ((minpoly R ℓ).natDegree - 1) = 0 := by rw [hres, h0, mul_zero]
    have hRK := congrArg (algebraMap R K) hR
    rw [← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK] at hRK
    have hsep : (minpoly K ℓ).Separable := Algebra.IsSeparable.isSeparable K ℓ
    have hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1 :=
      natDegree_derivative_le _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff,
      one_pow, one_mul] at hRK
    exact resultant_ne_zero _ _ hsep hRK
  · intro z hz
    obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant (minpoly R ℓ)
      (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')
    have hev := congrArg (aeval ℓ) hpq
    simp only [map_add, map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev
    have hadjK : Algebra.adjoin K {ℓ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj,
        IntermediateField.top_toSubalgebra]
    have hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ})) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [Submodule.mem_one]
      have hyint : IsIntegral R y := adjoin_le_integralClosure hℓ hy
      have htr : IsIntegral R (Algebra.trace K L (z * y)) := Algebra.isIntegral_trace (hz.mul hyint)
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
      exact ⟨r, by simpa [Algebra.traceForm_apply] using hr⟩
    rw [traceForm_dualSubmodule_adjoin R K hadjK hℓ] at hzmem
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem
    have hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ)) := by
      rw [hFK, derivative_map, aeval_map_algebraMap]
    rw [hd]
    have hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ} := aeval_mem_adjoin_singleton R ℓ
    have hw' : w ∈ Algebra.adjoin R {ℓ} := hw
    have key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) =
        ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) *
          (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹) := by
      rw [hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]
      ring
    rw [key]
    by_cases hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0
    · rw [hd0, zero_mul, mul_zero]
      exact zero_mem _
    · rw [mul_inv_cancel₀ hd0, mul_one]
      exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'
end DiscrAdjoin
end GroundTheory.Heights₂.Heights.ComplexSets
