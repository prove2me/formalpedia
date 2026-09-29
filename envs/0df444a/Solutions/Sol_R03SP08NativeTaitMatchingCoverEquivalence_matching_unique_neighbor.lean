-- Prove2me | solution 1 for R03SP08NativeTaitMatchingCoverEquivalence.matching_unique_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:18.55137+00:00
-- url     : https://prove2.me/submissions/9ed89f92-851d-487c-9248-5281adb7d933

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only joint native-model equivalence for the Tait interface.  A proper
Fin 3 edge labeling of a cubic graph is equivalent to a cover by three native
perfect matchings.  The theorem is an exact witness reformulation only; it
does not prove existence for planar bridgeless cubic graphs.
-/
namespace R03SP08NativeTaitMatchingCoverEquivalence

open CubicP3Partition

universe u
variable {V : Type u} [Fintype V]

structure ThreePerfectMatchingCover (G : SimpleGraph V) where
  M : Fin 3 → SimpleGraph V
  perfect : ∀ k, CubicP3Partition.PerfectMatching G (M k)
  cover : G ≤ ⨆ k, M k

def ProperThree
    (G : SimpleGraph V)
    (C : SimpleGraph.EdgeLabeling G (Fin 3)) : Prop :=
  ∀ ⦃u v w : V⦄ (huv : G.Adj u v) (huw : G.Adj u w),
    v ≠ w → C.get u v huv ≠ C.get u w huw


end R03SP08NativeTaitMatchingCoverEquivalence

open R03SP08NativeTaitMatchingCoverEquivalence
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
    {G M : SimpleGraph V}
    (hM : CubicP3Partition.PerfectMatching G M)
    {u v w : V} (hv : M.Adj u v) (hw : M.Adj u w) :
    v = w := by
  obtain ⟨z, hz⟩ := (Nat.card_eq_one_iff_exists.mp (hM.2 u))
  have hvz := hz (⟨v, hv⟩ : {x : V // M.Adj u x})
  have hwz := hz (⟨w, hw⟩ : {x : V // M.Adj u x})
  exact congrArg Subtype.val (hvz.trans hwz.symm)

