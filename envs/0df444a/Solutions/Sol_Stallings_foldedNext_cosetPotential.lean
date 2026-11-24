-- Prove2me | solution 1 for Stallings.foldedNext_cosetPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:24.10821+00:00
-- url     : https://prove2.me/submissions/20cef1f3-e67f-48ac-b875-4a7f24d65c4e

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_CosetEquivalent_trans
import Theorems.Thm_Stallings_CosetEquivalent_right_mul
import Theorems.Thm_Stallings_foldRel_cosetPotential
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff



set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (base : V) (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) {v t : V} {x : Letter}
    (hnext : (foldAutomaton G base).next v x = some t) :
    CosetEquivalent H (potential t) (potential v * letterEval x) := by
  change foldedNext G v x = some t at hnext
  have hv : v = foldRep G v := by
    unfold foldedNext at hnext
    split at hnext
    · assumption
    · simp at hnext
  have hcore : foldedNextCore G v x = some t := by
    change (if v = foldRep G v then foldedNextCore G v x else none) = some t at hnext
    rw [if_pos hv] at hnext
    exact hnext
  by_cases hne : (foldTargets G v x).Nonempty
  · unfold foldedNextCore at hcore
    rw [dif_pos hne] at hcore
    have ht : foldRep G ((foldTargets G v x).min' hne) = t := by
      injection hcore
    subst t
    let q := (foldTargets G v x).min' hne
    have hq : q ∈ foldTargets G v x := Finset.min'_mem _ _
    rcases Finset.mem_filter.mp hq with ⟨_, u, huv, hedge⟩
    have hqPot : CosetEquivalent H (potential (foldRep G q)) (potential q) :=
      foldRel_cosetPotential G H potential hpotential (foldRep_rel G q)
    have hedgePot : CosetEquivalent H (potential q) (potential u * letterEval x) :=
      hpotential hedge
    have huvPot : CosetEquivalent H (potential u) (potential v) :=
      foldRel_cosetPotential G H potential hpotential huv
    exact CosetEquivalent.trans hqPot <| CosetEquivalent.trans hedgePot
      (CosetEquivalent.right_mul huvPot (letterEval x))
  · unfold foldedNextCore at hcore
    rw [dif_neg hne] at hcore
    simp at hcore
end Stallings
