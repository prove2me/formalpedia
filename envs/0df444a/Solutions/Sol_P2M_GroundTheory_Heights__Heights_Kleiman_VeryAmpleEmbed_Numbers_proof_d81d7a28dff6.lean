-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleEmbed_Numbers_proof_d81d7a28dff6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:19.611982+00:00
-- url     : https://prove2.me/submissions/57ad9ff7-2964-4fd2-8326-9a6f08008f04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleEmbedNumbers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_proof_1c887bca4a14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_proof_28dc9e797b4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDegree_proof_8023612bf403
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_proof_ca6c5fc10660


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
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleEmbed.Numbers
theorem _root_.solution (hSecs : VeryAmpleSecs.Statement.{u, w})
    (hHilb : VeryAmpleHilbert.Statement.{u, w}) : VeryAmpleEmbed.Numbers.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h hV n hZ
  exact ⟨VeryAmpleDim.proof k Ω N y n Q r h hZ hV,
    VeryAmpleDegree.proof VeryAmpleDim.proof hSecs hHilb k Ω N y n Q r h hZ hV⟩
end VeryAmpleEmbed.Numbers
end GroundTheory.Heights₂.Heights.Kleiman
