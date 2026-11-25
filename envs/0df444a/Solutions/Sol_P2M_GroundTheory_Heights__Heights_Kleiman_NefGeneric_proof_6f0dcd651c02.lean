-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_NefGeneric_proof_6f0dcd651c02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:48.701776+00:00
-- url     : https://prove2.me/submissions/807d71ac-c173-4df5-a920-ce38aed8c1fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_curveClosure_d5266bbc86d1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace NefGeneric
theorem _root_.solution (hC : ConservationOfDegree.Statement.{u, w}) :
    NefGeneric.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 hM pp _ hpp
  have : pp.IsPrime := hpp.isPrime
  obtain ⟨hconst, hmap⟩ := curveClosure (S := S) pp
  have hpp' := hpp
  rw [← hmap] at hpp'
  have key := hC S F Ω N x M 𝔪 h𝔪 _ inferInstance hconst hpp'
  rw [hmap] at key
  rw [key]
  refine finsum_nonneg fun G => ?_
  split_ifs with hG
  · exact mul_nonneg (Int.natCast_nonneg _) (hM G (le_sup_right.trans hG.1.1.2) hG.2)
  · exact le_rfl
end NefGeneric
end GroundTheory.Heights₂.Heights.Kleiman
