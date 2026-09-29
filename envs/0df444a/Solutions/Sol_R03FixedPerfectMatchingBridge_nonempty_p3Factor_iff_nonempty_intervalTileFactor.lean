-- Prove2me | solution 1 for R03FixedPerfectMatchingBridge.nonempty_p3Factor_iff_nonempty_intervalTileFactor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:46.863568+00:00
-- url     : https://prove2.me/submissions/36d66b70-fd7a-49c0-98bf-5c6529db121b

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_e1150db1c7_w64_fixed_perfect_matching_bridge_v1

namespace R03FixedPerfectMatchingBridge

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

lemma perfectMatching_isMatchingRelation
    {G M : SimpleGraph V} (hM : PerfectMatching G M) :
    IsMatchingRelation M := by
  classical
  intro v a b hav hbv
  have hcard : Fintype.card {w : V // M.Adj v w} = 1 := by
    simpa [CubicP3Partition.degree, Nat.card_eq_fintype_card] using hM.2 v
  obtain ⟨w, hw⟩ := (Fintype.card_eq_one_iff.mp hcard)
  have ha : (⟨a, hav⟩ : {w : V // M.Adj v w}) = w := hw _
  have hb : (⟨b, hbv⟩ : {w : V // M.Adj v w}) = w := hw _
  exact congrArg Subtype.val (ha.trans hb.symm)

lemma p3Path_iff_intervalTile
    (G M : SimpleGraph V)
    (hMsub : M ≤ G)
    (hMmatch : IsMatchingRelation M)
    {a b c : V} :
    P3PathProp G a b c ↔ IntervalTile G M a b c := by
  constructor
  · rintro ⟨hab_ne, hbc_ne, hac_ne, hab, hbc⟩
    refine ⟨hab_ne, hbc_ne, hac_ne, ?_⟩
    by_cases hmab : M.Adj a b
    · right
      left
      refine ⟨hmab, ?_⟩
      by_cases hmbc : M.Adj b c
      · exact False.elim (hac_ne (hMmatch ((M.adj_comm a b).mp hmab) hmbc))
      · exact ⟨hbc, hmbc⟩
    · by_cases hmbc : M.Adj b c
      · right
        exact Or.inr ⟨⟨hab, hmab⟩, hmbc⟩
      · left
        exact ⟨⟨hab, hmab⟩, ⟨hbc, hmbc⟩⟩
  · rintro ⟨hab_ne, hbc_ne, hac_ne, htiles⟩
    refine ⟨hab_ne, hbc_ne, hac_ne, ?_⟩
    rcases htiles with hff | hmf | hfm
    · exact ⟨hff.1.1, hff.2.1⟩
    · exact ⟨hMsub hmf.1, hmf.2.1⟩
    · exact ⟨hfm.1.1, hMsub hfm.2⟩

lemma fin3_pairwise_distinct {α : Type u} (i : α) :
    (i, (0 : Fin 3)) ≠ (i, (1 : Fin 3)) ∧
    (i, (1 : Fin 3)) ≠ (i, (2 : Fin 3)) ∧
    (i, (0 : Fin 3)) ≠ (i, (2 : Fin 3)) := by
  simp


end R03FixedPerfectMatchingBridge

open R03FixedPerfectMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
    (G M : SimpleGraph V)
    (hMsub : M ≤ G)
    (hMmatch : IsMatchingRelation M) :
    Nonempty (CubicP3Partition.P3Factor G) ↔
      Nonempty (IntervalTileFactor G M) := by
  constructor
  · rintro ⟨p⟩
    refine ⟨{
      blockCount := p.blockCount
      place := p.place
      tile := ?_ }⟩
    intro i
    apply (p3Path_iff_intervalTile G M hMsub hMmatch).mp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have : (i, (0 : Fin 3)) = (i, (1 : Fin 3)) := p.place.injective h
      exact (fin3_pairwise_distinct i).1 this
    · intro h
      have : (i, (1 : Fin 3)) = (i, (2 : Fin 3)) := p.place.injective h
      exact (fin3_pairwise_distinct i).2.1 this
    · intro h
      have : (i, (0 : Fin 3)) = (i, (2 : Fin 3)) := p.place.injective h
      exact (fin3_pairwise_distinct i).2.2 this
    · exact ⟨p.edge01 i, p.edge12 i⟩
  · rintro ⟨t⟩
    refine ⟨{
      blockCount := t.blockCount
      place := t.place
      edge01 := ?_
      edge12 := ?_ }⟩
    · intro i
      have hp := (p3Path_iff_intervalTile G M hMsub hMmatch).mpr (t.tile i)
      exact hp.2.2.2.1
    · intro i
      have hp := (p3Path_iff_intervalTile G M hMsub hMmatch).mpr (t.tile i)
      exact hp.2.2.2.2
