-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_proof_9412c221d80a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:50.257698+00:00
-- url     : https://prove2.me/submissions/7f593b69-0bd2-41c9-9c14-b0389fa81bef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_hasProjectiveDimensionLE_3df477c9653d

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
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
namespace GroundTheory.Heights₂.Heights
namespace AuslanderBuchsbaumDepthLower
theorem _root_.solution : AuslanderBuchsbaumDepthLower.Statement.{u} := by
  intro R _ _ _ M _ _ _ _ ℓ rs hpd hmem hrs
  obtain ⟨ms, hlen, hms, hreg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (maximalIdeal R) (rs.length - ℓ) (ModuleCat.of R M)
    (AuslanderBuchsbaumDepthLower.maximalIdeal_smul_top_lt_top M)
    (AuslanderBuchsbaumDepthLower.residueModule R)
    AuslanderBuchsbaumDepthLower.support_residueModule
    (fun i hi => AuslanderBuchsbaumDepthLower.subsingleton_ext_of_hasProjectiveDimensionLE rs hmem hrs ℓ
      (ModuleCat.of R M) hpd i (by omega))
  exact ⟨ms, hms, hreg.toIsWeaklyRegular, hlen⟩
end AuslanderBuchsbaumDepthLower
end GroundTheory.Heights₂.Heights
