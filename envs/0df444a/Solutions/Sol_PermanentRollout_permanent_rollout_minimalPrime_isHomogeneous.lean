-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_minimalPrime_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/548cda9b-aafd-4736-b7b1-d1046ce704f8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {ι σ R : Type*} [CommRing R]
    [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
    [SetLike σ R] [AddSubmonoidClass σ R]
    {𝒜 : ι → σ} [GradedRing 𝒜]
    {I p : Ideal R}
    (hI : I.IsHomogeneous 𝒜)
    (hp : p ∈ I.minimalPrimes) :
    p.IsHomogeneous 𝒜 := by
  let core : Ideal R := (p.homogeneousCore 𝒜).toIdeal
  have hcoreprime : core.IsPrime := hp.isPrime.homogeneousCore
  have hcore_le : core ≤ p := Ideal.toIdeal_homogeneousCore_le 𝒜 p
  have hIcore : I ≤ core := by
    change I ≤ (p.homogeneousCore 𝒜).toIdeal
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hp.le
  have hcoreeq : core = p :=
    le_antisymm hcore_le (hp.2 ⟨hcoreprime, hIcore⟩ hcore_le)
  rw [← hcoreeq]
  exact (p.homogeneousCore 𝒜).isHomogeneous
end PermanentRollout
