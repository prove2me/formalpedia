-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_exact_of_partition_751a789b2856
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:23:45.698956+00:00
-- url     : https://prove2.me/submissions/613d026a-6963-4488-879f-6306c9b14dea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_d_eq_9797a3782368
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_cone_d_1843881f320e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9


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
theorem _root_.solution {A : Type w} [Semiring A] [Module A V] (M : Cell U → Submodule R V)
    {i : ℕ} (z : Cech.Cochain (fun _ : Cell U => V) (i + 1))
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0)
    (a : Fin n → A) (ha : ∑ k ∈ U, a k = 1)
    (hmem : ∀ (K : Cech.Idx U i) (k : Fin n), k ∈ U → k ∉ K.1.1 →
      a k • onSet z (insert k K.1.1) ∈ M K.1) :
    ∃ t ∈ Cech.Cdeg (fun _ : Cell U => V) M i,
      Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i t = z := by
  refine ⟨fun K => ∑ k ∈ U, a k • coneY k z K.1.1, fun K _ => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k hk => ?_
    unfold coneY
    split_ifs with h
    · rw [smul_zero]; exact zero_mem _
    · rw [smul_comm]; exact zsmul_mem (hmem K k hk h) _
  · funext K
    rw [d_eq]
    have hY : ∀ j ∈ K.1.1, onSet (fun I => ∑ k ∈ U, a k • coneY k z I.1.1 :
        Cech.Cochain (fun _ : Cell U => V) i) (K.1.1.erase j) =
          ∑ k ∈ U, a k • coneY k z (K.1.1.erase j) := by
      intro j hj
      unfold onSet
      rw [dif_pos ⟨by rw [Finset.card_erase_of_mem hj, K.2]; rfl,
        (Finset.erase_subset _ _).trans K.1.2.2⟩]
    rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
    calc ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • ∑ k ∈ U, a k • coneY k z (K.1.1.erase j)
        = ∑ k ∈ U, a k • ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) := by
          simp_rw [Finset.smul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      _ = ∑ k ∈ U, a k • z K := Finset.sum_congr rfl fun k hk => by rw [cone_d hz hk K]
      _ = z K := by rw [← Finset.sum_smul, ha, one_smul]
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Partition
