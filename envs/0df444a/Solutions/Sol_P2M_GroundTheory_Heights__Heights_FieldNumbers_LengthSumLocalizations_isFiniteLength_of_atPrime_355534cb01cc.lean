-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isFiniteLength_of_atPrime_355534cb01cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:50.298823+00:00
-- url     : https://prove2.me/submissions/e0bad9e3-7aed-4d80-b522-2120ef89a21c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_isSimpleModule_quot_maximalIdeal_1dd42758d047

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Module TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
variable {B : Type*} [CommRing B]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
theorem _root_.solution (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] (M : Type*) [AddCommGroup M] [Module C M]
    [instB : Module B M] [instT : IsScalarTower B C M] (hM : IsFiniteLength C M) :
    IsFiniteLength B M := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  revert instB instT
  induction hM with
  | of_subsingleton => intro _ _; exact .of_subsingleton
  | @of_simple_quotient M _ _ N hs hN ih =>
    intro _ _
    have hN' : IsFiniteLength B (N.restrictScalars B) := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    have := isSimpleModule_quot_maximalIdeal 𝔪 C
    have : IsSimpleModule B (M ⧸ N.restrictScalars B) :=
      IsSimpleModule.congr ((Submodule.Quotient.restrictScalarsEquiv B N).trans
        (e.restrictScalars B))
    exact .of_simple_quotient hN'
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
