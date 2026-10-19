-- Prove2me | solution 1 for SoficGroups.almostCentralizerCluster_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/5f8ca80f-28bb-4536-8612-7a1f933d3bca

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (p q : AlmostCentralizerElement σ tolerance) :
    almostCentralizerCluster hgap p = almostCentralizerCluster hgap q ↔
      5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V := by
  exact Quotient.eq
end SoficGroups
