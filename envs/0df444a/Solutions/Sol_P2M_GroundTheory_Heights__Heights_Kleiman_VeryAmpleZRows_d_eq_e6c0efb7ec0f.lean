-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_d_eq_e6c0efb7ec0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:55.084734+00:00
-- url     : https://prove2.me/submissions/699ce8db-0b99-406e-a849-ad1689876a03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_idx_949d3e04df5f

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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {n : ℕ} {U : Finset (Fin n)}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
theorem _root_.solution {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
