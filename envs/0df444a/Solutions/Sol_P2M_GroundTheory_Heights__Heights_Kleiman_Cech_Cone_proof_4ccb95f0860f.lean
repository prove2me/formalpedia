-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_proof_4ccb95f0860f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:09.417041+00:00
-- url     : https://prove2.me/submissions/51dee008-a841-4bca-8e32-16ea263a6f9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_mul_self_b354143a435a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_key_8a3d6f160b9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483

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
open Cech.Cone
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace Cech.Cone
theorem _root_.solution : Cech.Cone.Statement.{u, v} := by
  intro R _ V _ _ N J
  refine ⟨?_, ?_, fun z hz I K => const hz I K⟩
  · intro W i₀ hi₀ i z hz hW hJ
    have hWs : ∀ A, onSet z A ∈ W := by
      intro A; unfold onSet; split_ifs
      · exact hW _
      · exact W.zero_mem
    have hJs : ∀ A, ¬ J ⊆ A → onSet z A = 0 := by
      intro A hA; unfold onSet; split_ifs
      · exact hJ _ hA
      · rfl
    have hcoc : ∀ L : Finset (Fin (N + 1)), L.card = i + 1 + 1 + 1 →
        ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
      intro L hL
      have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), Finset.subset_univ L⟩, hL⟩
      rw [d_eq] at h
      exact h
    refine ⟨fun I => coneY i₀ z I.1.1, fun I => ?_, fun I hI => ?_, ?_⟩
    · change coneY i₀ z I.1.1 ∈ W
      unfold coneY; split_ifs
      · exact W.zero_mem
      · exact zsmul_mem (hWs _) _
    · change coneY i₀ z I.1.1 = 0
      unfold coneY; split_ifs
      · rfl
      · rw [hJs _ fun hs => hI fun x hx =>
          (Finset.mem_insert.mp (hs hx)).resolve_left fun (e : x = i₀) => hi₀ (e ▸ hx), smul_zero]
    · funext K
      rw [d_eq, ← onSet_idx z K]
      have hK : K.1.1.card = i + 1 + 1 := K.2
      have hY : ∀ j ∈ K.1.1, onSet (fun I => coneY i₀ z I.1.1 :
          Cech.Cochain (fun _ : StdCell N => V) i) (K.1.1.erase j) = coneY i₀ z (K.1.1.erase j) := by
        intro j hj
        unfold onSet
        rw [dif_pos (by rw [Finset.card_erase_of_mem hj, hK]; rfl)]
      rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
      generalize K.1.1 = Kf at hK ⊢
      by_cases h : i₀ ∈ Kf
      · rw [Finset.sum_eq_single i₀]
        · rw [coneY, if_neg (Finset.notMem_erase i₀ Kf), Finset.insert_erase h, smul_smul,
            sgn_mul_self, one_smul]
        · intro j hj hne
          rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
        · exact fun h' => absurd h h'
      · have hc := hcoc (insert i₀ Kf) (by rw [Finset.card_insert_of_notMem h, hK])
        rw [Finset.sum_insert h, Finset.erase_insert h] at hc
        have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
        have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY i₀ z (Kf.erase j) =
            -(Cech.sgn (insert i₀ Kf) i₀ •
              ∑ j ∈ Kf, Cech.sgn (insert i₀ Kf) j • onSet z ((insert i₀ Kf).erase j)) := by
          rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : i₀ ≠ j := fun e => h (e ▸ hj)
          have hni : i₀ ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
          rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
            sgn_key h hj, neg_smul]
        rw [hs, hb, smul_neg, neg_neg, smul_smul, sgn_mul_self, one_smul]
  · intro hJne i₀ hi₀ z hz hJ
    obtain ⟨j, hj⟩ := hJne
    funext I
    let I₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{i₀}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    rw [const hz I I₀]
    exact hJ I₀ fun hs => hi₀ (Finset.mem_singleton.mp (hs hj) ▸ hj)
end Cech.Cone
end GroundTheory.Heights₂.Heights.Kleiman
