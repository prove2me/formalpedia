-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_LineBundle_proof_28c071628e88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:57.161939+00:00
-- url     : https://prove2.me/submissions/f5067791-3785-4328-ae48-91c201f93328

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofFirst_mods_7cb70bc2bc0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofSecond_mods_63f974983985

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace LineBundle
theorem _root_.solution : LineBundle.Statement := by
  intro S _ N Ω _ _ x
  exact ⟨fun Q => ⟨ofFirst Q, ofFirst_mods Q⟩, fun Q' => ⟨ofSecond Q', fun i h => ofSecond_mods Q' h⟩⟩
end LineBundle
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
