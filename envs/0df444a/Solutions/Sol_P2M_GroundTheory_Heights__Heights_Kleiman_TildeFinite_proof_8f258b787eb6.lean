-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TildeFinite_proof_8f258b787eb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:43.936408+00:00
-- url     : https://prove2.me/submissions/1441a60e-4344-40ab-877d-83af5405ba59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_injective_fa47452d8f92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_res_bcc5079ec5bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedH_injective_3c4c852e48a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Transport_proof_0f907ba81f5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TildeTail_proof_fa6492dcadb7


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
namespace TildeFinite
theorem _root_.solution (h : SerreFinite.Statement.{u, w}) : TildeFinite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M i c
  have hT := Cech.Transport.proof (N + 1) (Finset.univ : Finset (Fin (N + 1))) S (locSys S N M.coneSub)
    (fun _ : StdCell N => ConeLaurent S x) locResS (supportRes S x) (degLoc M.coneGraded c) (M.coneDeg c)
    M.cellConeS M.cellConeS_res (fun I _ hm => Submodule.mem_map_of_mem hm) M.cellConeS_injective
    (fun _ => rfl) i
  have : Module.Finite S (Cech.Hdeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS i) :=
    h S N M.coneSub M.coneGraded M.coneSub_finite i c
  have : Module.Finite S
      (Cech.Hdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) i) :=
    Module.Finite.of_surjective _ hT.2
  exact Module.Finite.of_injective (M.embedH c i) (M.embedH_injective c i)
end TildeFinite
end GroundTheory.Heights₂.Heights.Kleiman
