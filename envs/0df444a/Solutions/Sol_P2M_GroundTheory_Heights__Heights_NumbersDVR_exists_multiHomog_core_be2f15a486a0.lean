-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_core_be2f15a486a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:32.54217+00:00
-- url     : https://prove2.me/submissions/ba95a6c6-3fb7-4d73-b87b-7fe49244087b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_of_isHomogeneous_lex_28d8cf3999da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f


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
theorem _root_.solution {W : Ideal (MRing ι R)} (hW : W.IsPrime) :
    ∃ W' : Ideal (MRing ι R), W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ W' ≤ W ∧
      (∀ J : Ideal (MRing ι R), IsMultiHomogIdeal J → J ≤ W → J ≤ W') ∧
      (∀ (x : MRing ι R) (γ : K → ℕ), IsMultiHomog x γ → x ∈ W → x ∈ W') := by
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  refine ⟨(W.homogeneousCore
      (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal,
    hW.homogeneousCore, isMultiHomogIdeal_of_isHomogeneous_lex e (Ideal.homogeneousCore _ W).isHomogeneous,
    Ideal.toIdeal_homogeneousCore_le _ W, ?_, ?_⟩
  · intro J hJ hJW
    have hJh := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJW
  · intro x γ hx hxW
    refine Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨lexRelabel e γ, ?_⟩ hxW
    rw [mem_weightedHomogeneousSubmodule]
    intro d hd
    rw [weight_comp_addMonoidHom, hx hd]
end GroundTheory.Heights₂.Heights.NumbersDVR
