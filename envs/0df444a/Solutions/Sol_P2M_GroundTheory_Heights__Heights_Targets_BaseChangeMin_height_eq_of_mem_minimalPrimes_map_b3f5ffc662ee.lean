-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_eq_of_mem_minimalPrimes_map_b3f5ffc662ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:06.924129+00:00
-- url     : https://prove2.me/submissions/cc914548-25c5-4fb7-9473-0c10e398b5f4

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_comap_of_mem_minimalPrimes_map_9e10c22ffe7b
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_comap_of_mem_minimalPrimes_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    Q.height = 𝔭.height := by
  have := flat_mvPolynomial_map (σ := σ) (F := F) (F' := F')
  have : Q.IsPrime := hQ.1.1
  have hc := comap_of_mem_minimalPrimes_map 𝔭 Q hQ
  have : Q.LiesOver 𝔭 := ⟨hc.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  have h0 : (Q.map (Ideal.Quotient.mk
      (𝔭.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F'))))).height = 0 := by
    have hQ' : Q ∈ (𝔭.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F'))).minimalPrimes := hQ
    rw [Ideal.minimalPrimes_eq_comap] at hQ'
    obtain ⟨Q', hQ'm, hQ'e⟩ := hQ'
    have : Q'.IsPrime := hQ'm.1.1
    rw [← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hQ'm
  rw [h0, add_zero]
end GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
