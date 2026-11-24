-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:51.306263+00:00
-- url     : https://prove2.me/submissions/c455defe-285b-479b-826f-559aeb799840

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
theorem _root_.solution {u f : MRing ι R} {α : K → ℕ} (hf : IsMultiHomog f α) (γ : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) (γ + α) (u * f) =
      weightedHomogeneousComponent (blockWeight ι) γ u * f := by
  letI := weightedGradedAlgebra R (blockWeight ι)
  have hmem : f ∈ weightedHomogeneousSubmodule R (blockWeight ι) α :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule R (blockWeight ι)) (a := u) (i := γ) hmem
  have key : ∀ (x : MRing ι R) (m : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) x m : MRing ι R) =
        weightedHomogeneousComponent (blockWeight ι) m x :=
    fun x m => weightedDecomposition.decompose'_apply R (blockWeight ι) x m
  rw [key, key] at h
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR
