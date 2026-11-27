-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_proof_7dd0f5b01e22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:04:01.004621+00:00
-- url     : https://prove2.me/submissions/976022d1-e0e1-4cfa-bf7c-69de9c7bd7be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_of_inv_1108d97397dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_pow_of_mem_7659ef21cbb7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_mono_afd05f439d9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_exists_partition_c437fe6b702e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_const_4bc76094e94d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_exact_of_partition_751a789b2856
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Partition_onSet_idx_f72ebc720009


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
open VeryAmpleZColumns
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleZColumns
theorem _root_.solution : VeryAmpleZColumns.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hV I
  have hH : ∀ j, h j ∈ H.sub I := fun j => (Submodule.mem_iInf _).mp (hV.mem_secs j) I

  have hne : ∃ k, h k ≠ 0 := by
    obtain ⟨w, hw, -⟩ := exists_partition hV I 1
    by_contra hall
    simp only [not_exists, not_not] at hall
    simp [hall] at hw
  obtain ⟨k0, hk0⟩ := hne
  let J0 : Cech.Idx (support h) 0 :=
    ⟨⟨{k0}, Finset.singleton_nonempty k0, Finset.singleton_subset_iff.mpr ((mem_support h).mpr hk0)⟩,
      Finset.card_singleton k0⟩
  refine ⟨fun J J' hJJ' => mono hH hJJ', fun J e he => ?_, fun b _ hb => hb J0, ?_, ?_⟩
  ·
    refine Submodule.subset_span ⟨0, ?_⟩
    rw [pow_zero, one_smul, mul_zero]
    change e ∈ (G.toSubSystem.twist (twistSys S x 0)).sub I
    rw [SubSystem.twist_twistSys_zero]
    exact he
  ·
    intro s hs hds
    have hconst := Cech.Partition.const hds
    refine ⟨s J0, ?_, fun J => hconst J J0⟩
    have hex : ∀ J : Cech.Idx (support h) 0, ∃ n, ∀ m, n ≤ m →
        xProd J.1 ^ m • s J0 ∈ (G.toSubSystem.twist (H.toSubSystem.pow (J.1.1.card * m))).sub I :=
      fun J => by
        have := exists_pow_of_mem (G := G.toSubSystem) hH (hs J (Set.mem_univ _))
        rwa [hconst J J0] at this
    choose f hf using hex
    obtain ⟨m, hm1, hfm⟩ : ∃ m, 1 ≤ m ∧ ∀ J, f J ≤ m :=
      ⟨Finset.univ.sup f + 1, by omega, fun J => (Finset.le_sup (Finset.mem_univ J)).trans (Nat.le_succ _)⟩
    obtain ⟨w, hw, hwinv⟩ := exists_partition hV I m
    have hb : s J0 = ∑ k, w k • (h k ^ m • s J0) := by
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hw, one_smul]
    rw [hb]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : h k = 0
    · rw [hk, zero_pow (by omega), zero_smul, smul_zero]; exact zero_mem _
    · let Jk : Cech.Idx (support h) 0 :=
        ⟨⟨{k}, Finset.singleton_nonempty k, Finset.singleton_subset_iff.mpr ((mem_support h).mpr hk)⟩,
          Finset.card_singleton k⟩
      have h1 := hf Jk m (hfm Jk)
      have hx : xProd Jk.1 = h k := Finset.prod_singleton _ _
      have hc : Jk.1.1.card * m = 0 + m := by
        show ({k} : Finset (Fin (r + 1))).card * m = 0 + m
        rw [Finset.card_singleton]; ring
      rw [hx, hc] at h1
      have h2 := smul_mem_twist_of_inv (hwinv k) h1
      change _ ∈ (G.toSubSystem.twist (twistSys S x 0)).sub I at h2
      rw [SubSystem.twist_twistSys_zero] at h2
      exact h2
  ·
    intro p s hs hds
    have hex : ∀ J : Cech.Idx (support h) (p + 1), ∃ n, ∀ m, n ≤ m →
        xProd J.1 ^ m • s J ∈ (G.toSubSystem.twist (H.toSubSystem.pow (J.1.1.card * m))).sub I :=
      fun J => exists_pow_of_mem (G := G.toSubSystem) hH (hs J (Set.mem_univ _))
    choose f hf using hex
    obtain ⟨m, hm1, hfm⟩ : ∃ m, 1 ≤ m ∧ ∀ J, f J ≤ m :=
      ⟨Finset.univ.sup f + 1, by omega, fun J => (Finset.le_sup (Finset.mem_univ J)).trans (Nat.le_succ _)⟩
    obtain ⟨w, hw, hwinv⟩ := exists_partition hV I m
    refine Cech.Partition.exact_of_partition (A := Ω) _ s hds (fun k => w k * h k ^ m) ?_ ?_
    · rw [← hw]
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      have : h k = 0 := by
        by_contra hne
        exact hk ((mem_support h).mpr hne)
      rw [this, zero_pow (by omega), mul_zero]
    · intro K k hk hkK
      let L : Cech.Idx (support h) (p + 1) :=
        ⟨⟨insert k K.1.1, Finset.insert_nonempty _ _, Finset.insert_subset hk K.1.2.2⟩, by
          rw [Finset.card_insert_of_notMem hkK, K.2]⟩
      rw [show Cech.Partition.onSet s (insert k K.1.1) = s L from Cech.Partition.onSet_idx s L]
      have h1 := hf L m (hfm L)
      have hx : xProd L.1 = h k * xProd K.1 := Finset.prod_insert hkK
      have hc : L.1.1.card * m = K.1.1.card * m + m := by
        show (insert k K.1.1).card * m = _
        rw [Finset.card_insert_of_notMem hkK]; ring
      rw [hx, hc] at h1
      have h2 := smul_mem_twist_of_inv (hwinv k) h1
      refine Submodule.subset_span ⟨m, ?_⟩
      have e : xProd K.1 ^ m • (w k * h k ^ m) • s L = w k • (h k * xProd K.1) ^ m • s L := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
      rw [e]
      exact h2
end VeryAmpleZColumns
end GroundTheory.Heights₂.Heights.Kleiman
