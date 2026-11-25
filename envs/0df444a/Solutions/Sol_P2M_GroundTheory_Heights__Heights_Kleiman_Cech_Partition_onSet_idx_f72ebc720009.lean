-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:49.673526+00:00
-- url     : https://prove2.me/submissions/46fff598-8625-4cce-8cdb-6680885ba292

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition

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
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V]
  [Module R V]
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
theorem _root_.solution {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by
  unfold onSet
  rw [dif_pos ⟨I.2, I.1.2.2⟩]
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
