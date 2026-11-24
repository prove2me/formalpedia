-- Prove2me | solution 1 for Stallings.foldRel_cosetPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:48.42641+00:00
-- url     : https://prove2.me/submissions/477dafd4-ee51-47ae-a7fa-d9b5d88f1e2e

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
import Theorems.Thm_Stallings_CosetEquivalent_refl
import Theorems.Thm_Stallings_CosetEquivalent_symm
import Theorems.Thm_Stallings_CosetEquivalent_trans
import Theorems.Thm_Stallings_CosetEquivalent_right_mul
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


section
namespace Stallings
namespace foldRel
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
end foldRel
namespace InverseMultigraph
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
end InverseMultigraph
namespace CosetEquivalent
end CosetEquivalent
private theorem cosetBool_eq_true (H : Subgroup Free) (g h : Free) :
    cosetBool H g h = true ↔ CosetEquivalent H g h := by
  classical
  by_cases hh : CosetEquivalent H g h <;> simp [cosetBool, hh]
end Stallings
end

set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) {v w : V}
    (hvw : foldRel G v w) : CosetEquivalent H (potential v) (potential w) := by
  classical
  let r : V → V → Bool := fun a b => cosetBool H (potential a) (potential b)
  have hr : IsFoldCongruence G r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      exact (cosetBool_eq_true H _ _).2 (CosetEquivalent.refl H (potential a))
    · intro a b hab
      apply (cosetBool_eq_true H _ _).2
      exact CosetEquivalent.symm ((cosetBool_eq_true H _ _).1 hab)
    · intro a b c hab hbc
      apply (cosetBool_eq_true H _ _).2
      exact CosetEquivalent.trans ((cosetBool_eq_true H _ _).1 hab)
        ((cosetBool_eq_true H _ _).1 hbc)
    · intro a b x u t hab hedgeU hedgeT
      apply (cosetBool_eq_true H _ _).2
      have hab' : CosetEquivalent H (potential a) (potential b) :=
        (cosetBool_eq_true H _ _).1 hab
      have hu : CosetEquivalent H (potential u) (potential a * letterEval x) :=
        hpotential hedgeU
      have ht : CosetEquivalent H (potential t) (potential b * letterEval x) :=
        hpotential hedgeT
      exact CosetEquivalent.trans hu <| CosetEquivalent.trans
        (CosetEquivalent.right_mul hab' (letterEval x)) (CosetEquivalent.symm ht)
  exact (cosetBool_eq_true H _ _).1 (hvw r hr)
end Stallings
