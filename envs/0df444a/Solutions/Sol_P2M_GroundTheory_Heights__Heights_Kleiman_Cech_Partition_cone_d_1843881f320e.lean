-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_cone_d_1843881f320e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:12:16.486361+00:00
-- url     : https://prove2.me/submissions/6b869898-33a0-44d3-9170-6062ad9b955f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_key_8a3d6f160b9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a


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
theorem _root_.solution {i : ℕ} {z : Cech.Cochain (fun _ : Cell U => V) (i + 1)}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0) {k : Fin n} (hk : k ∈ U)
    (K : Cech.Idx U (i + 1)) :
    ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) = z K := by
  have hcoc : ∀ L : Finset (Fin n), L ⊆ U → L.card = i + 1 + 1 + 1 →
      ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
    intro L hLU hL
    have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), hLU⟩, hL⟩
    rw [d_eq] at h
    exact h
  rw [← onSet_idx z K]
  have hK : K.1.1.card = i + 1 + 1 := K.2
  have hKU : K.1.1 ⊆ U := K.1.2.2
  generalize K.1.1 = Kf at hK hKU ⊢
  by_cases h : k ∈ Kf
  · rw [Finset.sum_eq_single k]
    · rw [coneY, if_neg (Finset.notMem_erase k Kf), Finset.insert_erase h, smul_smul,
        Cech.Cone.sgn_mul_self, one_smul]
    · intro j hj hne
      rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
    · exact fun h' => absurd h h'
  · have hc := hcoc (insert k Kf) (Finset.insert_subset hk hKU)
      (by rw [Finset.card_insert_of_notMem h, hK])
    rw [Finset.sum_insert h, Finset.erase_insert h] at hc
    have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
    have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY k z (Kf.erase j) =
        -(Cech.sgn (insert k Kf) k •
          ∑ j ∈ Kf, Cech.sgn (insert k Kf) j • onSet z ((insert k Kf).erase j)) := by
      rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : k ≠ j := fun e => h (e ▸ hj)
      have hni : k ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
      rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
        Cech.Cone.sgn_key h hj, neg_smul]
    rw [hs, hb, smul_neg, neg_neg, smul_smul, Cech.Cone.sgn_mul_self, one_smul]
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
