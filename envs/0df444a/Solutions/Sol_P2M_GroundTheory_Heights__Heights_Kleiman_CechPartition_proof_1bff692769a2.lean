-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechPartition_proof_1bff692769a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:04.756694+00:00
-- url     : https://prove2.me/submissions/a1471e4f-4dc4-418c-8c3c-3bc2179f72d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechPartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CechPartition
theorem _root_.solution : CechPartition.Statement.{u, v, w} := by
  intro S _ Ω _ E _ _ _ n U M m a b j hjU hab ha hb hloc p s hs hds

  let T : Subring Ω :=
    { carrier := {c | ∀ I, ∀ z ∈ M I, c • z ∈ M I}
      mul_mem' := fun {x y} hx hy I z hz => by rw [mul_smul]; exact hx I _ (hy I z hz)
      one_mem' := fun I z hz => by rwa [one_smul]
      add_mem' := fun {x y} hx hy I z hz => by rw [add_smul]; exact (M I).add_mem (hx I z hz) (hy I z hz)
      zero_mem' := fun I z _ => by rw [zero_smul]; exact (M I).zero_mem
      neg_mem' := fun {x} hx I z hz => by rw [neg_smul]; exact (M I).neg_mem (hx I z hz) }
  have hT : ∀ c ∈ T, ∀ I, ∀ z ∈ M I, c • z ∈ M I := fun c hc => hc
  let b' : Fin m → T := fun k => ⟨b k, hb k⟩

  have hspan : Ideal.span (Set.range b') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (∑ k, (⟨a k, ha k⟩ : T) * b' k) = 1 := Subtype.ext (by simp [b', hab])
    rw [← h1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

  have hex : ∀ (k : Fin m) (K : Cech.Idx U p), ∃ e0 : ℕ, j k ∉ K.1.1 →
      b k ^ e0 • Cech.Partition.onSet s (insert (j k) K.1.1) ∈ M K.1 := by
    intro k K
    by_cases hk : j k ∈ K.1.1
    · exact ⟨0, fun h => absurd hk h⟩
    · let I' : Cell U := ⟨insert (j k) K.1.1, Finset.insert_nonempty _ _, Finset.insert_subset (hjU k) K.1.2.2⟩
      have hI' : I'.1.card = p + 1 + 1 := by
        change (insert (j k) K.1.1).card = p + 1 + 1
        rw [Finset.card_insert_of_notMem hk, K.2]
      have hz : Cech.Partition.onSet s (insert (j k) K.1.1) ∈ M I' := by
        rw [show insert (j k) K.1.1 = (⟨I', hI'⟩ : Cech.Idx U (p + 1)).1.1 from rfl, Cech.Partition.onSet_idx]
        exact (Submodule.mem_pi.mp hs) ⟨I', hI'⟩ (Set.mem_univ _)
      obtain ⟨e0, he0⟩ := hloc k K.1 I' rfl _ hz
      exact ⟨e0, fun _ => he0⟩
  choose f hf using hex
  obtain ⟨e, he⟩ : ∃ e, ∀ k K, f k K ≤ e := by
    obtain ⟨e, he⟩ := (Set.finite_range (fun x : Fin m × Cech.Idx U p => f x.1 x.2)).bddAbove
    exact ⟨e, fun k K => he ⟨(k, K), rfl⟩⟩

  have hpow := Ideal.span_pow_eq_top (Set.range b') hspan e
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at hpow
  obtain ⟨c, hc⟩ := hpow

  let wt : Fin n → Ω := fun i => ∑ k ∈ Finset.univ.filter (fun k => j k = i), (c k : Ω) * b k ^ e
  have hw : ∑ i ∈ U, wt i = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun k _ => hjU k)]
    have h := congrArg Subtype.val hc
    simpa [b'] using h
  refine Cech.Partition.exact_of_partition M s hds wt hw ?_
  intro K i _ hiK
  simp only [wt, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain rfl := (Finset.mem_filter.mp hk).2
  rw [mul_smul, ← Nat.sub_add_cancel (he k K), pow_add, mul_smul]
  exact hT _ (c k).2 _ _ (hT _ (pow_mem (show b k ∈ T from hb k) _) _ _ (hf k K hiK))
end CechPartition
end GroundTheory.Heights₂.Heights.Kleiman
