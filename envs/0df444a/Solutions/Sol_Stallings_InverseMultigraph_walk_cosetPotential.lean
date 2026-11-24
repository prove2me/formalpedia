-- Prove2me | solution 1 for Stallings.InverseMultigraph.walk_cosetPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:48.830796+00:00
-- url     : https://prove2.me/submissions/9ef17ea1-367d-4d96-ba10-5848592d5257

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_CosetEquivalent_refl
import Theorems.Thm_Stallings_CosetEquivalent_trans
import Theorems.Thm_Stallings_CosetEquivalent_right_mul
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
namespace InverseMultigraph
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V] (G : InverseMultigraph V) (H : Subgroup Free)
    (potential : V → Free) (hpotential : HasCosetPotential G H potential) :
    ∀ {v z : V} {w : Word}, G.Walk v w z →
      CosetEquivalent H (potential z) (potential v * wordEval w) := by
  intro v z w hwalk
  induction hwalk with
  | nil v =>
      simpa [wordEval_nil] using CosetEquivalent.refl H (potential v)
  | @cons v u z x w edge tail ih =>
      have hedge : CosetEquivalent H (potential u) (potential v * letterEval x) :=
        hpotential edge
      simpa [wordEval_cons, mul_assoc] using
        CosetEquivalent.trans ih (CosetEquivalent.right_mul hedge (wordEval w))
end InverseMultigraph
end Stallings
