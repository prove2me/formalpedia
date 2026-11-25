-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_const_zero_e15e840f64ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:52.821363+00:00
-- url     : https://prove2.me/submissions/34d861a9-abbc-4eaf-a2a0-a9889bed5291

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_idx_949d3e04df5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_pair_816866761f25

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
theorem _root_.solution {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) (I K : Cech.Idx U 0) : s I = s K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (ha ▸ Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (hb ▸ Finset.mem_singleton_self b)
  rw [← onSet_idx s I, ← onSet_idx s K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hs haU hbU h
  · rfl
  · exact (onSet_pair hs hbU haU h).symm
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
