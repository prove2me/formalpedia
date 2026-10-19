-- Prove2me | solution 1 for SoficGroups.ExceptionalRankOffset.exists_common_log_rank_offset_except
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/78a0fe93-9cc6-4293-b6da-cb710b1f3f19

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_common_log_rank_offset
import Theorems.Thm_SoficGroups_ExceptionalRankOffset_rankDropCount_le_goodSubtype_add_exceptions

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ExceptionalRankOffset
open Filter Topology
open scoped BigOperators
namespace SoficGroups.ExceptionalRankOffset
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (x y : ι → ℝ) (eta H : ℝ)
    (hx : ∀ i ∈ G, 0 < x i)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hH : 0 < H)
    (hcomparison : ∀ i ∈ G, (1 - eta) * x i ≤ y i) :
    ∃ r ∈ Set.Ico 0 H,
      SoficGroups.rankDropCount
          (fun i => Real.log (x i))
          (fun i => Real.log (y i)) H r ≤
        (G.card : ℝ) * |Real.log (1 - eta)| / H +
          (((Finset.univ : Finset ι) \ G).card : ℝ) := by
  obtain ⟨r, hr, hbound⟩ := SoficGroups.exists_common_log_rank_offset
    (fun i : {i // i ∈ G} => x i.1)
    (fun i : {i // i ∈ G} => y i.1)
    eta H
    (fun i => hx i.1 i.2)
    heta0 heta1 hH
    (fun i => hcomparison i.1 i.2)
  have hbound' :
      SoficGroups.rankDropCount
        (fun i : {i // i ∈ G} => Real.log (x i.1))
        (fun i : {i // i ∈ G} => Real.log (y i.1)) H r ≤
          (G.card : ℝ) * |Real.log (1 - eta)| / H := by
    simpa only [Fintype.card_coe] using hbound
  refine ⟨r, hr, ?_⟩
  calc
    SoficGroups.rankDropCount
        (fun i => Real.log (x i))
        (fun i => Real.log (y i)) H r ≤
      SoficGroups.rankDropCount
          (fun i : {i // i ∈ G} => Real.log (x i.1))
          (fun i : {i // i ∈ G} => Real.log (y i.1)) H r +
        (((Finset.univ : Finset ι) \ G).card : ℝ) :=
        rankDropCount_le_goodSubtype_add_exceptions G
          (fun i => Real.log (x i)) (fun i => Real.log (y i)) H r
    _ ≤ (G.card : ℝ) * |Real.log (1 - eta)| / H +
        (((Finset.univ : Finset ι) \ G).card : ℝ) :=
        add_le_add hbound' (le_refl _)
end SoficGroups.ExceptionalRankOffset
