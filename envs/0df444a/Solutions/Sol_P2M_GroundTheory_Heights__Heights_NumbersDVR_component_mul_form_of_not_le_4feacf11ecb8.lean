-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_not_le_4feacf11ecb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:57.86569+00:00
-- url     : https://prove2.me/submissions/92a4effe-ffc7-432b-bfa7-00f126977170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {v g : MRing ι R} {β : K → ℕ} (hg : IsMultiHomog g β)
    {n : K → ℕ} (hn : ¬ β ≤ n) :
    weightedHomogeneousComponent (blockWeight ι) n (v * g) = 0 := by
  letI := weightedGradedAlgebra R (blockWeight ι)
  have hmem : g ∈ weightedHomogeneousSubmodule R (blockWeight ι) β :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg
  have h := DirectSum.coe_decompose_mul_of_right_mem_of_not_le
    (weightedHomogeneousSubmodule R (blockWeight ι)) (a := v) hmem hn
  rw [← h]
  exact (weightedDecomposition.decompose'_apply R (blockWeight ι) (v * g) n).symm
end GroundTheory.Heights₂.Heights.NumbersDVR
