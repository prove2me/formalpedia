-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SectionNef_proof_7ba5c90ed895
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:23.394039+00:00
-- url     : https://prove2.me/submissions/6a5aa1d6-62dd-49f7-8602-97d1ba12e621

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSectionNef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_hilbFn_sub_le_of_regular_a8f58f594e0c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open MvPolynomial NumbersDVR
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace SectionNef
theorem _root_.solution : SectionNef.Statement := by
  intro K _ _ ι _ F _ P hP _ b f g hs
  have hev := hilbFn_sub_le_of_regular hP hs
  unfold intNum eventualValue
  split_ifs with h
  · obtain ⟨m, hm1, hm2⟩ := (h.choose_spec.and hev).exists
    rw [← hm1]
    simp only [mixedDiff, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      Matrix.cons_val_zero, diffStep]
    linarith
  · exact le_rfl
end SectionNef
end GroundTheory.Heights₂.Heights.Model
