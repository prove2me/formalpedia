-- Prove2me | solution 2 for WeakGoldbach.verified_range_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T20:24:40.41478+00:00
-- url     : https://prove2.me/submissions/30b104ef-871a-4df3-8c9c-548f02bf5d2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Theorems.Thm_GoldbachSieve_witnesses_cover_finset
import Theorems.Thm_WeakGoldbach_verified_range_pointwise_sieve_coverage

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

open WeakGoldbach

theorem solution (b : ℕ) (hb : b < 4000000000001) :
    ((Finset.Icc (max 4 (4 * 10 ^ 14 + b * 1000000))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
        (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 9781 (4 * 10 ^ 14 + b * 1000000 - 9781)
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1)) 2000000000 := by
  refine GoldbachSieve.witnesses_cover_finset
    (A := (Finset.Icc (max 4 (4 * 10 ^ 14 + b * 1000000))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
        (fun n => Even n))
    (smallBound := 9781)
    (lo := 4 * 10 ^ 14 + b * 1000000 - 9781)
    (hi := min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))
    (cutoff := 2000000000) ?_
  intro n hn
  obtain ⟨hlo0, heven⟩ := Finset.mem_filter.mp hn
  obtain ⟨hbnd, hbnd'⟩ := Finset.mem_Icc.mp hlo0
  have hblocklo : 4 * 10 ^ 14 + b * 1000000 ≤ n :=
    le_trans (le_max_right 4 (4 * 10 ^ 14 + b * 1000000)) hbnd
  have hlo14 : 4 * 10 ^ 14 ≤ n := by
    refine le_trans ?_ hblocklo
    simpa using Nat.le_add_right 2 (4 * 10 ^ 14)
  have hhi18 : n ≤ 4 * 10 ^ 18 := le_trans hbnd' (min_le_left _ _)
  obtain ⟨p, q, hp, hp9781, hqmem, hpq⟩ :=
    verified_range_pointwise_sieve_coverage n hlo14 hhi18 heven
  obtain ⟨hqIcc, hcard⟩ := Finset.mem_filter.mp hqmem
  obtain ⟨hqlo', hqhi'⟩ := Finset.mem_Icc.mp hqIcc
  have hqlo : max 2 (4 * 10 ^ 14 + b * 1000000 - 9781) ≤ q :=
    le_trans (max_le_max (Nat.le_refl 2)
      (Nat.sub_le_sub_right hblocklo 9781)) hqlo'
  have hqhi : q ≤ min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1) :=
    le_trans hqhi' hbnd'
  -- E01: the goal is `List.Mem p (List.filter (fun b => decide (Nat.Prime b))
  -- (List.range' 2 (9781 + 1 - 2)))`, i.e. membership in a `filter` over an
  -- `Icc`, so it needs `mem_filter.mpr` and then the `Icc` pair.
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.Prime.two_le hp, hp9781⟩, hp⟩, q, ?_, hpq.symm⟩
  -- E02: the same two-level shape for the unfolded `survivors` filter.
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, hcard⟩
