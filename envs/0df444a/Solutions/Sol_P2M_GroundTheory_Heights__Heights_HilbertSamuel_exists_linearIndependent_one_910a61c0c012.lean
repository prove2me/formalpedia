-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_linearIndependent_one_910a61c0c012
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:26.380472+00:00
-- url     : https://prove2.me/submissions/13d506ae-adec-4e61-956d-cfa44f071001

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent

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
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (E : HermitianBundle.{0} K) (h : 0 < bundleRank E) :
    ∃ s : Fin 1 → E.carrier, LinearIndependent (𝓞 K) s := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank (R := 𝓞 K) (M := E.carrier)
    (v := Fin.elim0) (linearIndependent_empty_type) h
  exact ⟨_, hx⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
