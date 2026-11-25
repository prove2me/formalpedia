-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistSections_proof_af54bc9ab3cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:20.992181+00:00
-- url     : https://prove2.me/submissions/1bee8256-4ce2-413b-94a8-c7fb06e37191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_piece_le_secs_7b0b7b96dc1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_secs_le_of_surjective_f10808922dce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_finite_quot_e423b00c1db3


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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TwistSections
theorem _root_.solution (h : SerreOnto.Statement.{u, u}) : TwistSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N y hy
  obtain ⟨c₀, hc₀⟩ := h S N (Poly S N ⧸ primeOf (S := S) y) (primeQuotGraded y) (finite_quot _)
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun n hn => le_antisymm ?_ (coordGraded_piece_le_secs y n)⟩
  exact secs_le_of_surjective y hy n (hc₀ n ((Int.self_le_toNat c₀).trans (by exact_mod_cast hn)))
end TwistSections
end GroundTheory.Heights₂.Heights.Kleiman
