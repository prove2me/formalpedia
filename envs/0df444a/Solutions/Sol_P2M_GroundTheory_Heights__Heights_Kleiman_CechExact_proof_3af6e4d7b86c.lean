-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:32.271333+00:00
-- url     : https://prove2.me/submissions/83b634a9-d675-4427-9a69-77285f529f00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locResS_mem_9778806aef35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locMap_mem_b2b662503dcb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_comp_locResS_e33ebeba7576
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_injective_d760537304b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_locMap_eq_zero_6e4ca001f07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locResS_comp_aed20a079c45


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
universe u v
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CechExact
theorem _root_.solution (hdsq : CechDSq.Statement.{u, max u v}) (hdeg : DegLocExact.Statement.{u, v}) :
    CechExact.Statement.{u, v} := by
  intro S _ _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c
  have hex := hdeg S N M' M M'' 𝓜' 𝓜 𝓜'' f g hf hg hfg c
  exact Cech.longExact (A := locSys S N M') (B := locSys S N M) (C := locSys S N M'')
    (ρA := locResS) (ρB := locResS) (ρC := locResS)
    (dA := degLoc 𝓜' c) (dB := degLoc 𝓜 c) (dC := degLoc 𝓜'' c)
    (φ := fun I => (locMap f.toLin I.1).restrictScalars S)
    (ψ := fun I => (locMap g.toLin I.1).restrictScalars S)
    (fun I J h x => locMap_comp_locResS f.toLin I J h x) (fun I J h x => locMap_comp_locResS g.toLin I J h x)
    (fun I x hx => degLoc_locMap_mem f c I x hx) (fun I x hx => degLoc_locMap_mem g c I x hx)
    (fun I => locMap_injective f.toLin hf I.1)
    (fun I x => locMap_locMap_eq_zero f.toLin g.toLin (fun m => hfg.apply_apply_eq_zero m) I.1 x)
    (fun I => (hex I).1) (fun I => (hex I).2)
    (fun I J h x hx => degLoc_locResS_mem 𝓜 c I J h x hx)
    (hdsq _ Finset.univ S (locSys S N M) locResS locResS_comp)
end CechExact
end GroundTheory.Heights₂.Heights.Kleiman
