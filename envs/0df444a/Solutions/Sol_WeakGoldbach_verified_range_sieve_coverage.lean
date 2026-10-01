-- Prove2me | solution 1 for WeakGoldbach.verified_range_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:13:54.528081+00:00
-- url     : https://prove2.me/submissions/cdcc9e19-35d3-48dd-8e35-f62c9be577ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_range_pointwise_sieve_coverage
import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution (b : Nat) (hb : b < 4000000000001) :
    ((Finset.Icc (max 4 (4 * 10 ^ 14 + b * 1000000))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
        (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 9781 (4 * 10 ^ 14 + b * 1000000 - 9781)
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1)) 2000000000 := by
  intro n hn
  have hnmem := Finset.mem_filter.mp hn
  have hbounds := Finset.mem_Icc.mp hnmem.1
  have hstart : 4 * 10 ^ 14 + b * 1000000 ≤ n := by
    exact le_trans (Nat.le_max_right _ _) hbounds.1
  have hend : n ≤ min (4 * 10 ^ 18)
      (4 * 10 ^ 14 + (b + 1) * 1000000 - 1) := hbounds.2
  have hpoint := WeakGoldbach.verified_range_pointwise_sieve_coverage n
      (le_trans (Nat.le_add_right _ _) hstart)
      (le_trans hend (Nat.min_le_left _ _))
      hnmem.2
  let p := Classical.choose hpoint
  have hpdata : Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 9781)
        (And (Membership.mem (GoldbachSieve.survivors (n - 9781) n 2000000000) q)
          (p + q = n))) := Classical.choose_spec hpoint
  let q := Classical.choose hpdata
  have hdata := Classical.choose_spec hpdata
  have hp : Nat.Prime p := hdata.1
  have hpbound : Nat.le p 9781 := hdata.2.1
  have hq := hdata.2.2.1
  have hsum := hdata.2.2.2
  have hqblock : q ∈ GoldbachSieve.survivors
      (4 * 10 ^ 14 + b * 1000000 - 9781)
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))
      2000000000 := by
    change q ∈ (Finset.Icc (max 2 (n - 9781)) n).filter
      (fun q => ((((Finset.Icc 2 2000000000).filter Nat.Prime).filter
        (fun r => r ∣ q ∧ r ≠ q)).card = 0)) at hq
    have hqmem := Finset.mem_filter.mp hq
    have hqbounds := Finset.mem_Icc.mp hqmem.1
    change q ∈ (Finset.Icc
      (max 2 (4 * 10 ^ 14 + b * 1000000 - 9781))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
      (fun q => ((((Finset.Icc 2 2000000000).filter Nat.Prime).filter
        (fun r => r ∣ q ∧ r ≠ q)).card = 0))
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · apply max_le
        · exact le_trans (Nat.le_max_left _ _) hqbounds.1
        · have hsub : 4 * 10 ^ 14 + b * 1000000 - 9781 ≤ n - 9781 :=
            Nat.sub_le_sub_right hstart 9781
          exact le_trans (le_trans hsub (Nat.le_max_right _ _)) hqbounds.1
      · exact le_trans hqbounds.2 hend
    · exact hqmem.2
  unfold GoldbachSieve.pairSums
  rw [Finset.mem_biUnion]
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpbound⟩, hp⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨q, hqblock, hsum⟩
