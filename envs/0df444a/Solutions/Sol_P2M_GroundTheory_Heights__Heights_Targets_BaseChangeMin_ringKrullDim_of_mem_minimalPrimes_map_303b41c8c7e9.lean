-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_ringKrullDim_of_mem_minimalPrimes_map_303b41c8c7e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:29.284315+00:00
-- url     : https://prove2.me/submissions/e0fb8614-edc7-4cbc-b3eb-f4ab0e9296ea

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_eq_of_mem_minimalPrimes_map_b3f5ffc662ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_add_ringKrullDim_quotient_d92c37b125a4
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_eq_of_mem_minimalPrimes_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_withBot_enat_cancel
import Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient


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
namespace GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ F' ⧸ Q) = ringKrullDim (MvPolynomial σ F ⧸ 𝔭) := by
  have : Q.IsPrime := hQ.1.1
  have h1 := height_add_ringKrullDim_quotient F' Q
  have h2 := height_add_ringKrullDim_quotient F 𝔭
  rw [height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ] at h1
  exact ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel h1 h2
end GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
