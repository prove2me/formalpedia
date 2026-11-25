-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Exists_proof_9fa489fa0269
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:09.685456+00:00
-- url     : https://prove2.me/submissions/56029c30-7378-447a-936a-fed96c9c131e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFilt_card_prime_eq_length_c94425c30737

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
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace PrimeFiltration.Exists
theorem _root_.solution : PrimeFiltration.Exists.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x M _ _ _ _ 𝓜 _ _
  let _ := 𝓜.isInternal.chooseDecomposition
  exact ⟨⟨𝓜.primeFilt⟩, fun F pp _ hpp => F.card_prime_eq_length pp hpp⟩
end PrimeFiltration.Exists
end GroundTheory.Heights₂.Heights.Kleiman
