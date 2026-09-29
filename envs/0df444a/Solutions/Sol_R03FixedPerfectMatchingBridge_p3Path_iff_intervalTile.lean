-- Prove2me | solution 1 for R03FixedPerfectMatchingBridge.p3Path_iff_intervalTile
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:54.633918+00:00
-- url     : https://prove2.me/submissions/8c416956-bd42-45ad-bfd7-0a1ff0a0190f

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


end R03FixedPerfectMatchingBridge

open R03FixedPerfectMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
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
