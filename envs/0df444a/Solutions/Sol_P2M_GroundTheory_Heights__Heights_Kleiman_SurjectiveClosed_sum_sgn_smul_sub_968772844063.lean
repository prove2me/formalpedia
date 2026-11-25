-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_smul_sub_968772844063
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:49.057396+00:00
-- url     : https://prove2.me/submissions/c351bee2-b340-4b90-83f9-62c5ed835eb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed

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
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {n : ℕ}
variable {U : Finset (Fin n)} {A : Type*} [AddCommGroup A]
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution (φ : Cell U → A) (J : Cech.Idx U 1) :
    ∑ j : J.1.1, Cech.sgn J.1.1 j • (φ (Cech.face J j).1 - φ J.1) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • φ (Cech.face J j).1 := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, Finset.sum_coe_sort J.1.1 (fun j => Cech.sgn J.1.1 j),
    Cech.sum_sgn_of_card_two J.2, zero_smul, sub_zero]
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
