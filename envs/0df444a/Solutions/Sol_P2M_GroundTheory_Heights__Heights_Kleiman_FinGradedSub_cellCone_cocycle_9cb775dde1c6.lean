-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_cocycle_9cb775dde1c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:50.259081+00:00
-- url     : https://prove2.me/submissions/8aeee53a-5a54-477d-8c1c-8fb639289ec1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_self_a6716700d2d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : Cech.d (locSys S N M.coneSub) locResS 0 z = 0)
    (K K' : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0)
    (hK : K.1.1 ⊆ support x) (hK' : K'.1.1 ⊆ support x) :
    M.cellCone K.1 (z K) = M.cellCone K'.1 (z K') := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · have : K = K' := Subtype.ext (Subtype.ext (ha.trans (hab ▸ hb.symm)))
    subst this; rfl
  let Kp : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, Finset.card_pair hab⟩
  have hKp : Kp.1.1 ⊆ support x := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hK (by rw [ha]; exact Finset.mem_singleton_self _)
    · exact hK' (by rw [hb]; exact hi)
  have hfa : ∀ j : Kp.1.1, (j : Fin (N + 1)) = a → Cech.face Kp j = K' := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K'.1.1
    rw [hj, hb, Finset.erase_insert (Finset.notMem_singleton.mpr hab)]
  have hfb : ∀ j : Kp.1.1, (j : Fin (N + 1)) = b → Cech.face Kp j = K := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K.1.1
    rw [hj, ha, Finset.pair_comm, Finset.erase_insert (Finset.notMem_singleton.mpr (Ne.symm hab))]
  have h0 := congrArg (M.cellCone Kp.1) (congrFun hz Kp)
  rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have hterm : ∀ j : Kp.1.1, M.cellCone Kp.1 (Cech.sgn Kp.1.1 j • locResS (Cech.face Kp j).1 Kp.1
      (Cech.face_subset Kp j) (z (Cech.face Kp j))) =
      Cech.sgn Kp.1.1 j • M.cellCone (Cech.face Kp j).1 (z (Cech.face Kp j)) := by
    intro j
    rw [map_zsmul, M.cellCone_of_subset hKp, M.cellCone_of_subset ((Cech.face_subset Kp j).trans hKp)]
    congr 1
    exact locCone_locRes M (Cech.face_subset Kp j) hKp _
  rw [Finset.sum_congr rfl fun j _ => hterm j] at h0
  rw [Fintype.sum_eq_add (⟨a, Finset.mem_insert_self a {b}⟩ : Kp.1.1)
    (⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ : Kp.1.1)
    (fun h => hab (congrArg Subtype.val h)) (fun j hj => ?_)] at h0
  · rw [hfa ⟨a, Finset.mem_insert_self a {b}⟩ rfl,
      hfb ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ rfl] at h0
    have hs : Cech.sgn Kp.1.1 b = -Cech.sgn Kp.1.1 a := by
      have := Cech.sum_sgn_of_card_two (J := Kp.1.1) Kp.2
      rw [show Kp.1.1 = {a, b} from rfl, Finset.sum_pair hab] at this
      linarith
    change Cech.sgn Kp.1.1 a • M.cellCone K'.1 (z K') + Cech.sgn Kp.1.1 b • M.cellCone K.1 (z K) = 0 at h0
    rw [hs, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h0
    have h1 := congrArg (Cech.sgn Kp.1.1 a • ·) h0
    simp only [smul_smul, Cech.sgn_mul_self, one_smul, smul_zero] at h1
    exact (sub_eq_zero.mp h1).symm
  · exfalso
    rcases Finset.mem_insert.mp j.2 with h | h
    · exact hj.1 (Subtype.ext h)
    · exact hj.2 (Subtype.ext (Finset.mem_singleton.mp h))
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
