-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_euler_certificate_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:35:52.801075+00:00
-- url     : https://prove2.me/submissions/ccda0f31-a77e-4e19-b3e0-0c56fdad12f8

import Definitions.Def_WilliamsonShmoys_TriangularEulerCertificate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hcert : HasTriangularEulerCertificate U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  rcases hcert with ⟨m, boundary, htri, hinc, hEuler⟩
  have hcard : U.edgeSet.ncard = Fintype.card U.edgeSet := by
    simpa using (Set.ncard_eq_toFinset_card U.edgeSet (Set.toFinite U.edgeSet))
  have hfaces : (∑ f : Fin m, (boundary f).card) = 3 * m := by
    calc
      (∑ f : Fin m, (boundary f).card) = ∑ _f : Fin m, 3 := by
        apply Finset.sum_congr rfl
        intro f hf
        exact htri f
      _ = 3 * m := by simp [Nat.mul_comm]
  have hface_inc :
      (∑ f : Fin m, (boundary f).card) =
        ∑ f : Fin m, ∑ e : U.edgeSet, (if e ∈ boundary f then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro f hf
    simp
  have hswap :
      (∑ f : Fin m, ∑ e : U.edgeSet, (if e ∈ boundary f then 1 else 0)) =
        ∑ e : U.edgeSet, ∑ f : Fin m, (if e ∈ boundary f then 1 else 0) := by
    rw [Finset.sum_comm]
  have hedges :
      (∑ e : U.edgeSet, ∑ f : Fin m, (if e ∈ boundary f then 1 else 0)) =
        2 * U.edgeSet.ncard := by
    calc
      (∑ e : U.edgeSet, ∑ f : Fin m, (if e ∈ boundary f then 1 else 0)) =
          ∑ e : U.edgeSet, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        exact hinc e
      _ = 2 * U.edgeSet.ncard := by
        rw [hcard]
        simp [Nat.mul_comm]
  have hincidence : 3 * m = 2 * U.edgeSet.ncard := by
    calc
      3 * m = ∑ f : Fin m, (boundary f).card := hfaces.symm
      _ = ∑ f : Fin m, ∑ e : U.edgeSet, (if e ∈ boundary f then 1 else 0) := hface_inc
      _ = ∑ e : U.edgeSet, ∑ f : Fin m, (if e ∈ boundary f then 1 else 0) := hswap
      _ = 2 * U.edgeSet.ncard := hedges
  omega
