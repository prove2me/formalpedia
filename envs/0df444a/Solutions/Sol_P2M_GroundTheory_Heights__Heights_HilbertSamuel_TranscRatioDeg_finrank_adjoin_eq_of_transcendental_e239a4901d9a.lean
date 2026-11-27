-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_eq_of_transcendental_e239a4901d9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:49.615695+00:00
-- url     : https://prove2.me/submissions/043b8276-d6e2-413e-857c-41d54581d03e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LinearIndependentAdjoinOfTranscendental
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_linearIndependent_adjoin_of_transcendental_6af103ce99cb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
open Polynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
theorem _root_.solution {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) :
    Module.finrank (IntermediateField.adjoin K {t})
      (IntermediateField.adjoin (IntermediateField.adjoin K {t}) (A : Set E)) = Module.finrank K A := by
  set L := IntermediateField.adjoin K {t}
  let a := Module.Free.chooseBasis K A
  have hind : LinearIndependent L (A.val ∘ a) :=
    linearIndependent_adjoin_of_transcendental A ht a.linearIndependent
  by_cases hfin : Module.Finite K A
  · have H : A.LinearDisjoint L := IntermediateField.LinearDisjoint.of_basis_left a hind
    have hr := H.adjoin_rank_eq_rank_left_of_isAlgebraic_left
    exact congrArg Cardinal.toNat hr
  · rw [Module.finrank_of_not_finite hfin]
    apply Module.finrank_of_not_finite
    intro hfin'
    apply hfin
    set M := IntermediateField.adjoin L (A : Set E)
    let f : Module.Free.ChooseBasisIndex K A → M :=
      fun k => ⟨A.val (a k), IntermediateField.subset_adjoin L _ (a k).2⟩
    have hf : LinearIndependent L f := LinearIndependent.of_comp M.val.toLinearMap hind
    have : Finite (Module.Free.ChooseBasisIndex K A) := hf.finite
    exact Module.Finite.of_basis a
end GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
