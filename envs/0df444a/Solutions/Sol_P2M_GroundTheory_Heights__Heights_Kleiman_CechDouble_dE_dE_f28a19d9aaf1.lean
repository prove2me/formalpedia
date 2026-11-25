-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dE_dE_f28a19d9aaf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:23.102467+00:00
-- url     : https://prove2.me/submissions/83f86201-d18d-4b78-8992-526a223cc716

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_proof_00587d327cc8


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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble
open Cech
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {m : ℕ} {U : Finset (Fin m)}
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble
theorem _root_.solution (p : ℕ) (s : Cochain (fun _ : Cell U => E) p) : dE S E U (p + 1) (dE S E U p s) = 0 :=
  CechDSq.proof m U S (fun _ => E) (Cech.idRes S E U) (fun _ _ _ _ _ => rfl) p s
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble
