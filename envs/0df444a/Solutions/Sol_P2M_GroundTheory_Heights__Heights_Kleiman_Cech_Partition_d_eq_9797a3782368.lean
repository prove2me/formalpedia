-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:09.272338+00:00
-- url     : https://prove2.me/submissions/4fc7f9aa-fe11-403b-89d8-2f40fb433705

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674


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
theorem _root_.solution {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
