-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_HypPairExists_proof_a0f8c9b04833
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:47.144933+00:00
-- url     : https://prove2.me/submissions/a91589cc-e12b-40c4-9e8a-c1284989256b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PHypPairExists
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace HypPairExists
theorem _root_.solution : HypPairExists.Statement := by
  intro E _ σ hσ h2 N J hJ hdet e he0 hee

  have hw : ∃ j, ∑ i, e i * J i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : e ᵥ* J = 0 := by
      ext j
      simpa [vecMul, dotProduct] using h j
    apply he0
    calc e = e ᵥ* (J * J⁻¹) := by rw [mul_nonsing_inv J hdet, vecMul_one]
      _ = (e ᵥ* J) ᵥ* J⁻¹ := by rw [vecMul_vecMul]
      _ = 0 := by rw [h0, zero_vecMul]
  obtain ⟨j, hj⟩ := hw
  have hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j := by
    simp only [hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp

  obtain ⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1 :=
    ⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by
      rw [hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩
  have hae : hf σ J a e = 1 := by
    rw [← hf_symm hσ hJ, hea, map_one]
  have haa : σ (hf σ J a a) = hf σ J a a := hf_symm hσ hJ a a
  set t : E := -(hf σ J a a) / 2 with ht_def
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have ht : t + σ t = -(hf σ J a a) := by
    rw [ht_def, map_div₀, map_neg, haa, hσ2]
    field_simp
    ring
  refine ⟨a + t • e, ?_, ?_⟩
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hea, hae, hee]
    linear_combination ht
  · rw [hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]
end HypPairExists
end GroundTheory.Heights₂.Heights.StrongApprox
