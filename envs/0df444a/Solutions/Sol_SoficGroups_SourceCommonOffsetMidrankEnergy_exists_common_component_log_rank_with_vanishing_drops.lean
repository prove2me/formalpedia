-- Prove2me | solution 1 for SoficGroups.SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_drops
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/03efcc33-782c-4ef1-9cde-5cb046a4d7c1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MidrankPermutationEnergy_rankDropCount_eq_sum_rankDecreasingVertices
import Theorems.Thm_SoficGroups_ExceptionalRankOffset_exists_common_log_rank_offsets_tendsto_zero_except
import Theorems.Thm_SoficGroups_SourceCommonOffsetMidrankEnergy_componentSizeComparison_of_not_mem

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonOffsetMidrankEnergy
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → ι → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hbad : Tendsto
      (fun n =>
        ((componentSizeComparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι,
            ((SoficGroups.MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (componentLogRank (Q n) (H n) (r n))
              (p n i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) := by
  classical
  let B : (n : ℕ) → Finset (ι × V n) :=
    fun n => componentSizeComparisonBad (Q n) (p n) (eta n)
  let E : (n : ℕ) → Finset (ι × V n) :=
    fun n => Finset.univ \ B n
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hpositive (n : ℕ) (e : ι × V n) (_he : e ∈ E n) :
      0 < realComponentSize (Q n) e.2 := by
    have hpart : (Q n).part e.2 ∈ (Q n).parts :=
      (Q n).part_mem.mpr (Finset.mem_univ e.2)
    have hnonempty := (Q n).nonempty_of_mem_parts hpart
    unfold realComponentSize SoficGroups.partitionComponentSize
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hcard (n : ℕ) :
      ((E n).card : ℝ) ≤
        (Fintype.card ι : ℝ) * (Fintype.card (V n) : ℝ) := by
    have hnat : (E n).card ≤ Fintype.card ι * Fintype.card (V n) := by
      simpa only [Fintype.card_prod] using
        (Finset.card_le_univ (E n))
    exact_mod_cast hnat
  have hcomparison (n : ℕ) (e : ι × V n) (he : e ∈ E n) :
      (1 - eta n) * realComponentSize (Q n) e.2 ≤
        realComponentSize (Q n) (p n e.1 e.2) := by
    apply componentSizeComparison_of_not_mem (Q n) (p n) (eta n)
      e.1 e.2
    exact (Finset.mem_sdiff.mp he).2
  have hexceptions : Tendsto
      (fun n =>
        (((Finset.univ : Finset (ι × V n)) \ E n).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by
    simpa [E, B] using hbad
  obtain ⟨r, hr, hdrop⟩ :=
    SoficGroups.ExceptionalRankOffset.exists_common_log_rank_offsets_tendsto_zero_except
        (fun n => ι × V n) E
        (fun n e => realComponentSize (Q n) e.2)
        (fun n e => realComponentSize (Q n) (p n e.1 e.2))
        eta H (fun n => (Fintype.card (V n) : ℝ))
        (Fintype.card ι : ℝ)
        hpositive heta0 heta1 hH hN hcard hcomparison
        heta hratio hexceptions
  have hrewrite (n : ℕ) :
      SoficGroups.rankDropCount
        (fun e : ι × V n => Real.log (realComponentSize (Q n) e.2))
        (fun e : ι × V n =>
          Real.log (realComponentSize (Q n) (p n e.1 e.2)))
        (H n) (r n) =
        ∑ i : ι,
          ((SoficGroups.MidrankPermutationEnergy.rankDecreasingVertices
            Finset.univ (componentLogRank (Q n) (H n) (r n))
            (p n i)).card : ℝ) := by
    simpa only [componentLogRank] using
      (SoficGroups.MidrankPermutationEnergy.rankDropCount_eq_sum_rankDecreasingVertices
        (fun x : V n => Real.log (realComponentSize (Q n) x))
        (p n) (H n) (r n))
  refine ⟨r, hr, ?_⟩
  simpa only [hrewrite] using hdrop
end SoficGroups.SourceCommonOffsetMidrankEnergy
