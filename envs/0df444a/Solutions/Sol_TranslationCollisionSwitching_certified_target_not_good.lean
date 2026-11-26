-- Prove2me | solution 1 for TranslationCollisionSwitching.certified_target_not_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:36.995146+00:00
-- url     : https://prove2.me/submissions/fa5e3eb9-feea-4c61-9d28-b76b9e50cc0d

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationCollisionSwitching_not_good_of_collision_le

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationCollisionSwitching
open TranslationReversal TranslationIntegration
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationCollisionSwitching.graphAdjDecidable
attribute [local instance] TranslationCollisionSwitching.vertexDecidableEq
namespace TranslationCollisionSwitching
theorem _root_.solution {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) :
    ¬ IsGood d G hG start (certifiedTarget (d := d) G hG q) k := by
  let qs : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.source, q.1.source_valid⟩
  let qf : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.finish, q.1.finish_valid⟩
  obtain ⟨t, ht, hcollision⟩ :=
    deviation_exists_collision_of_detour (d := d) G hG start q.1.sample qs qf
      q.1.endpoint_eq q.2
  apply not_good_of_collision_le (d := d) G hG start _ k t
  · have hc := q.1.length_le
    have hs := q.1.source_le
    have ht' : t ≤ internalTime q.1.source.1 +
        returnLength d G hG start q.1.sample.1 k
          ⟨q.1.source, q.1.source_valid⟩ := by
      simpa only [qs] using ht
    change t ≤ k
    omega
  · exact hcollision
end TranslationCollisionSwitching
