-- Prove2me | solution 1 for Stallings.run_cosetPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:58.891898+00:00
-- url     : https://prove2.me/submissions/5d573fcc-81af-4f95-9c5f-7ee38795d3a8

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_CosetEquivalent_trans
import Theorems.Thm_Stallings_CosetEquivalent_right_mul
import Theorems.Thm_Stallings_foldedNext_cosetPotential
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (base : V)
    (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) :
    ∀ {v t : V} {w : Word},
      (foldAutomaton G base).run v w = some t →
      CosetEquivalent H (potential t) (potential v * wordEval w) := by
  intro v t w hrun
  induction w generalizing v t with
  | nil =>
      simp only [InverseAutomaton.run, Option.some.injEq] at hrun
      subst t
      simp [CosetEquivalent]
  | cons x w ih =>
      simp only [InverseAutomaton.run] at hrun
      cases hnext : (foldAutomaton G base).next v x with
      | none => simp [hnext] at hrun
      | some u =>
          have htail : (foldAutomaton G base).run u w = some t := by
            simpa [hnext] using hrun
          have hstep := foldedNext_cosetPotential G base H potential hpotential hnext
          have htailPotential := ih htail
          have hcombined := CosetEquivalent.trans htailPotential
            (CosetEquivalent.right_mul hstep (wordEval w))
          simpa [wordEval_cons, mul_assoc] using hcombined
end Stallings
