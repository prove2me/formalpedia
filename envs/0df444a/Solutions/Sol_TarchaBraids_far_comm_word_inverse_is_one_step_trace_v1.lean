-- Prove2me | solution 1 for TarchaBraids.far_comm_word_inverse_is_one_step_trace_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T15:38:14.845187+00:00
-- url     : https://prove2.me/submissions/a40531a8-e1f9-4b61-8ada-e354d02a31ee

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

open BraidsLinksMCG TarchaBraids

theorem solution
    {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    GeomRelatorTrace n
      ((FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
        (FreeGroup.of j)⁻¹)⁻¹) := by
  let r : FreeGroup (Fin (n - 1)) :=
    FreeGroup.of j * FreeGroup.of i * (FreeGroup.of j)⁻¹ *
      (FreeGroup.of i)⁻¹
  have hr : r ∈ braidRels n := by
    simp only [braidRels, Set.mem_setOf_eq, Set.mem_union]
    left
    have hij' : 2 ≤ ((j : ℤ) - (i : ℤ)).natAbs := by
      rw [show (j : ℤ) - (i : ℤ) = -((i : ℤ) - (j : ℤ)) by ring,
        Int.natAbs_neg]
      exact hij
    exact ⟨j, i, hij', rfl⟩
  have hword :
      r =
        (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
          (FreeGroup.of j)⁻¹)⁻¹ := by
    change
      FreeGroup.of j * FreeGroup.of i * (FreeGroup.of j)⁻¹ *
          (FreeGroup.of i)⁻¹ =
        (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
          (FreeGroup.of j)⁻¹)⁻¹
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have ht : GeomRelatorTrace n r := by
    simpa using
      (GeomRelatorTrace.step (n := n) (w := 1) (u := 1) (r := r)
        (GeomRelatorTrace.nil (n := n)) hr)
  rw [← hword]
  exact ht
