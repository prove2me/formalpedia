-- Prove2me | solution 1 for TranslationCollisionSwitching.certifiedCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:04.186558+00:00
-- url     : https://prove2.me/submissions/5368aef8-d4c8-431a-9dc1-7f331b321f39

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationCollisionSwitching_recover_deviationRotation
public import Theorems.Thm_TranslationCollisionSwitching_returnEndpoint_congr
public import Theorems.Thm_TranslationCollisionSwitching_sideDart_rotation_congr

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
theorem _root_.solution {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (certifiedCode (d := d) G hG :
        CertifiedClassifiedReturn (d := d) G hG start k L →
          RotationSystem d V × (Fin L × Offset d)) := by
  intro q r hcode
  have htarget : certifiedTarget (d := d) G hG q =
      certifiedTarget (d := d) G hG r := congrArg Prod.fst hcode
  have hslot : (certifiedSlot (d := d) G hG q : ℕ) =
      (certifiedSlot (d := d) G hG r : ℕ) :=
    congrArg (fun z : RotationSystem d V × (Fin L × Offset d) ↦
      (z.2.1 : ℕ)) hcode
  have hold : certifiedOldOffset (d := d) G hG q =
      certifiedOldOffset (d := d) G hG r :=
    congrArg (fun z : RotationSystem d V × (Fin L × Offset d) ↦ z.2.2) hcode
  have hT : firstCollisionTime (d := d) G hG start
      (certifiedTarget (d := d) G hG q) =
      firstCollisionTime (d := d) G hG start
        (certifiedTarget (d := d) G hG r) :=
    congrArg (firstCollisionTime (d := d) G hG start) htarget
  have hwq := certified_collision_window (d := d) G hG q
  have hwr := certified_collision_window (d := d) G hG r
  have htime : internalTime q.1.source.1 = internalTime r.1.source.1 := by
    change firstCollisionTime (d := d) G hG start
        (certifiedTarget (d := d) G hG q) -
          (internalTime q.1.source.1 + 1) =
      firstCollisionTime (d := d) G hG start
        (certifiedTarget (d := d) G hG r) -
          (internalTime r.1.source.1 + 1) at hslot
    omega
  have hindex : q.1.source.1 = r.1.source.1 := by
    apply Fin.ext
    simp only [internalTime] at htime
    omega
  let qs : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.source, q.1.source_valid⟩
  let rs : ValidDeviation d G hG start r.1.sample.1 k :=
    ⟨r.1.source, r.1.source_valid⟩
  have hvq := deviation_orbitVertex_eq_of_le (d := d) G hG start q.1.sample qs
    (le_refl (internalTime qs.1.1))
  have hvr := deviation_orbitVertex_eq_of_le (d := d) G hG start r.1.sample rs
    (le_refl (internalTime rs.1.1))
  have hoffset : q.1.source.2 = r.1.source.2 := by
    calc
      q.1.source.2 = certifiedTarget (d := d) G hG q
          (orbitVertex d G hG start q.1.sample.1 (internalTime q.1.source.1)) :=
        (deviationRotation_apply_source (d := d) G hG start q.1.sample.1 q.1.source).symm
      _ = certifiedTarget (d := d) G hG q
          (orbitVertex d G hG start (certifiedTarget (d := d) G hG q)
            (internalTime q.1.source.1)) :=
        congrArg (certifiedTarget (d := d) G hG q) hvq.symm
      _ = certifiedTarget (d := d) G hG r
          (orbitVertex d G hG start (certifiedTarget (d := d) G hG r)
            (internalTime r.1.source.1)) := by rw [htarget, htime]
      _ = certifiedTarget (d := d) G hG r
          (orbitVertex d G hG start r.1.sample.1 (internalTime r.1.source.1)) :=
        congrArg (certifiedTarget (d := d) G hG r) hvr
      _ = r.1.source.2 :=
        deviationRotation_apply_source (d := d) G hG start r.1.sample.1 r.1.source
  have hsource : q.1.source = r.1.source := Prod.ext hindex hoffset
  have hsampleVal : q.1.sample.1 = r.1.sample.1 := by
    calc
      q.1.sample.1 = recoverRotation (d := d) G hG start
          (certifiedTarget (d := d) G hG q) q.1.source.1
          (certifiedOldOffset (d := d) G hG q) :=
        (recover_deviationRotation (d := d) G hG start q.1.sample qs).symm
      _ = recoverRotation (d := d) G hG start
          (certifiedTarget (d := d) G hG r) r.1.source.1
          (certifiedOldOffset (d := d) G hG r) := by
        rw [htarget, hindex, hold]
      _ = r.1.sample.1 :=
        recover_deviationRotation (d := d) G hG start r.1.sample rs
  have hsample : q.1.sample = r.1.sample := Subtype.ext hsampleVal
  have hfinish : q.1.finish = r.1.finish := by
    have hendpoint :
        returnEndpoint d G hG start q.1.sample.1 k
            ⟨q.1.source, q.1.source_valid⟩ =
          returnEndpoint d G hG start r.1.sample.1 k
            ⟨r.1.source, r.1.source_valid⟩ :=
      returnEndpoint_congr (d := d) G hG start hsampleVal hsource
        q.1.source_valid r.1.source_valid
    have hsides : sideDart d G hG start q.1.sample.1 q.1.finish =
        sideDart d G hG start r.1.sample.1 r.1.finish := by
      apply (Dart.reverse G).injective
      exact q.1.endpoint_eq.symm.trans (hendpoint.trans r.1.endpoint_eq)
    have hsides' : sideDart d G hG start q.1.sample.1 q.1.finish =
        sideDart d G hG start q.1.sample.1 r.1.finish :=
      hsides.trans
        (sideDart_rotation_congr (d := d) G hG start hsampleVal r.1.finish).symm
    have hrvalid : IsValidDeviation d G hG start q.1.sample.1 r.1.finish := by
      simpa only [hsampleVal] using r.1.finish_valid
    have hvalid :
        (⟨q.1.finish, q.1.finish_valid⟩ :
          ValidDeviation d G hG start q.1.sample.1 k) =
        ⟨r.1.finish, hrvalid⟩ := by
      apply validSideDart_injective d G hG start q.1.sample
      exact hsides'
    exact congrArg Subtype.val hvalid
  apply Subtype.ext
  apply ClassifiedEligibleReturn.ext
  · exact hsample
  · exact hsource
  · exact hfinish
end TranslationCollisionSwitching
