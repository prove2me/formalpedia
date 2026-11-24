-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:04.17541+00:00
-- url     : https://prove2.me/submissions/6e31a197-0749-434f-acad-fb9e01a182ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827

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
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
theorem _root_.solution {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    (I K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz h
  · rfl
  · exact (onSet_pair hz h).symm
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
