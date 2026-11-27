-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CutNonempty_proof_ba2e58ffd458
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:16.150626+00:00
-- url     : https://prove2.me/submissions/bb4f6481-edd4-4f54-bce2-b25af8b6a520

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutNonempty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sub_le_twist_sup_span_d1f50341dc77

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
namespace CutNonempty
theorem _root_.solution (hO : CutOneGenerator.Statement.{u, w}) : CutNonempty.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs _
  by_contra hne
  push Not at hne
  exact hO k Ω N x n pp L s hW hL hs (sub_le_twist_sup_span hW.homog L s hne)
end CutNonempty
end GroundTheory.Heights₂.Heights.Kleiman
