-- Prove2me | solution 1 for SoficGroups.SourceCompressionMatching.transported_maximumOverlapPart_card_lt_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/320ce1b2-1687-46e6-8d4c-dd05a858449f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_maximumOverlapPart_mem
import Theorems.Thm_SoficGroups_partitionComponentSize_eq_card_of_mem
import Theorems.Thm_SoficGroups_SourceCompressionMatching_lt_exp_mul_of_equal_log_floor

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionMatching
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (C : Finset V) (hC : C ∈ Q.parts)
    (H r : ℝ) (hH : 0 < H) (x : V) (hx : x ∈ C)
    (hTx : T x ∈ SoficGroups.maximumOverlapPart Q
      (C.map T.toEmbedding))
    (hrank :
      SoficGroups.MidrankPermutationEnergy.offsetFloorRank
          (fun z : V =>
            Real.log (SoficGroups.partitionComponentSize Q z : ℝ))
          H r (T x) =
        SoficGroups.MidrankPermutationEnergy.offsetFloorRank
          (fun z : V =>
            Real.log (SoficGroups.partitionComponentSize Q z : ℝ))
          H r x) :
    ((SoficGroups.maximumOverlapPart Q
      (C.map T.toEmbedding)).card : ℝ) <
        Real.exp H * (C.card : ℝ) := by
  let D := SoficGroups.maximumOverlapPart Q (C.map T.toEmbedding)
  have hCne : C.Nonempty := Q.nonempty_of_mem_parts hC
  have hD : D ∈ Q.parts :=
    SoficGroups.maximumOverlapPart_mem Q (C.map T.toEmbedding)
      ((Finset.map_nonempty).2 hCne) (Finset.subset_univ _)
  have hsource : SoficGroups.partitionComponentSize Q x = C.card :=
    SoficGroups.partitionComponentSize_eq_card_of_mem Q C hC x hx
  have htarget : SoficGroups.partitionComponentSize Q (T x) = D.card :=
    SoficGroups.partitionComponentSize_eq_card_of_mem
      Q D hD (T x) hTx
  have hfloor :
      ⌊(Real.log (C.card : ℝ) + r) / H⌋ =
        ⌊(Real.log (D.card : ℝ) + r) / H⌋ := by
    simpa [SoficGroups.MidrankPermutationEnergy.offsetFloorRank,
      hsource, htarget] using hrank.symm
  have hxpos : (0 : ℝ) < C.card := by
    exact_mod_cast hCne.card_pos
  have hypos : (0 : ℝ) < D.card := by
    exact_mod_cast (Q.nonempty_of_mem_parts hD).card_pos
  exact lt_exp_mul_of_equal_log_floor hxpos hypos hH hfloor
end SoficGroups.SourceCompressionMatching
