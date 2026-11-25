-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_le_646124b8182c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:56.403682+00:00
-- url     : https://prove2.me/submissions/02216197-e5e4-42af-9735-0b9e980f1088

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b

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
theorem _root_.solution {v g : MRing ι R} {β : K → ℕ} (hg : IsMultiHomog g β) {n : K → ℕ}
    (hn : β ≤ n) :
    weightedHomogeneousComponent (blockWeight ι) n (v * g) =
      weightedHomogeneousComponent (blockWeight ι) (n - β) v * g := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le hn
  rw [add_comm β γ, add_tsub_cancel_right]
  exact component_mul_form_add hg γ
end GroundTheory.Heights₂.Heights.NumbersDVR
