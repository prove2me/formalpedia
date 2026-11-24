-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:44.863217+00:00
-- url     : https://prove2.me/submissions/336b66d1-9066-46d3-afd7-253781869c8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution (y : C) (X : Type*) [AddCommGroup X] [Module C X] [Subsingleton X] :
    Module.length C (QuotSMulTop y X) = 0 ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = 0 := by
  have : Subsingleton (QuotSMulTop y X) := (Submodule.mkQ_surjective _).subsingleton
  exact ⟨Module.length_eq_zero, Module.length_eq_zero⟩
end GroundTheory.Heights₂.Heights.LengthCutGlobal
