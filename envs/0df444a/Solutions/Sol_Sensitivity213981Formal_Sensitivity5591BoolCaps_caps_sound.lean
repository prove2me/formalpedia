-- Prove2me | solution 1 for Sensitivity213981Formal.Sensitivity5591BoolCaps.caps_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:57.072337+00:00
-- url     : https://prove2.me/submissions/1e8d7dcc-d576-41ae-bff3-9661fb56a36e

import Definitions.Def_Sensitivity213981Formal_Label5591Joint
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_coherent_of_zero
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_coherent_restrict
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_double_of_exclusion
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_marked_of_exclusion
import Theorems.Thm_Sensitivity213981Formal_Sensitivity10007BoolCaps_source_of_exclusion


namespace Sensitivity213981Formal
section
/- The actual Paley-10007 label satisfies the Bool-valued exclusion interfaces
used by the graded-candidate and residual-cap proofs. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Sensitivity10007BoolCaps
open Sensitivity10007Labeling
open scoped Classical BigOperators
noncomputable section





theorem bit_eq_iff (c : Fin 2) (b : Bool) : c = colorBit b ↔ bit c = b := by
  fin_cases c <;> cases b <;> decide

theorem bit_ne_iff (c : Fin 2) (b : Bool) : c ≠ colorBit b ↔ bit c ≠ b :=
  not_congr (bit_eq_iff c b)



variable {V : Type} [Fintype V] [DecidableEq V]

theorem mismatch_eq (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (color : V → Bool) (v : V) :
    ZL.mismatch R ell A (fun w => colorBit (color w)) v =
      CandidateCoherence.mismatch R (boolLabel ell) A color v := by
  ext w
  change (w ∈ A.filter (fun z => R v z ∧ ell (v,z) ≠ colorBit (color z))) ↔
    (w ∈ A.filter (fun z => R v z ∧ bit (ell (v,z)) ≠ color z))
  simp only [Finset.mem_filter, bit_ne_iff]

theorem ordinary_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (q a : ℕ)
    (hex : ∀ J : ZL.OrdinaryIndex V a, ¬ (ZL.ordinaryFamily R q a).bad J ell) :
    CandidateCoherence.NoOrdinary R (boolLabel ell) q a := by
  intro A ha color hg
  let J : ZL.OrdinaryIndex V a :=
    ⟨A,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,ha⟩⟩
  apply hex J
  refine ⟨fun w => colorBit (color w),?_⟩
  intro v hv
  simpa only [mismatch_eq] using hg v hv



























end
end Sensitivity10007BoolCaps






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Convert the joint 5591 exclusions to every semantic cap used by the recurrence. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Sensitivity5591BoolCaps
open Sensitivity10007Labeling Sensitivity10007BoolCaps Sensitivity5591Labeling
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem perfect_of_exclusion (R : V → V → Prop) (ell : V × V → Fin 2) (a m : ℕ)
    (hex : ∀ J : ZL.MarkedIndex V a m, ¬ (ThreeBoundPerfectFamily.family R a m).bad J ell) :
    ResidualCaps.DominatorCardBound R (boolLabel ell) m a := by
  intro A M color hdis hM hdom hz
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcompl : A' ⊆ Mᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr fun hm => Finset.disjoint_left.mp hdis (hA' hv) hm
  let MI : (Finset.univ : Finset V).powersetCard m :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let J : ZL.MarkedIndex V a m := ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hcompl,hcard⟩⟩⟩
  apply hex J
  refine ⟨?_,fun w => colorBit (color w),?_⟩
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun v hv => hdom v hv w (hA' hw)⟩
  · exact coherent_restrict R ell A A' M hA' _ (coherent_of_zero R ell A M color hz)

theorem ordinary_of_joint (R : V → V → Prop) (ell : V × V → Fin 2)
    (hex : Caps.JointExclusions R ell) (q : Fin 9) :
    CandidateCoherence.NoOrdinary R (boolLabel ell) q.val (Caps.ordinaryA q) :=
  ordinary_of_exclusion R ell q.val (Caps.ordinaryA q) (hex.ordinary q)

theorem marked_of_joint (R : V → V → Prop) (ell : V × V → Fin 2)
    (hex : Caps.JointExclusions R ell) (i : Fin 12) :
    ResidualCaps.MarkedCardBound R (boolLabel ell) (Caps.marked i).q (Caps.marked i).m
      (Caps.marked i).B (Caps.marked i).a :=
  marked_of_exclusion R ell _ _ _ _ (hex.marked i)

theorem caps_sound (R : V → V → Prop) (ell : V × V → Fin 2)
    (hex : Caps.JointExclusions R ell) :
    ThreeBoundRankNumeric.CapsSound R (boolLabel ell) ThreeBoundOrdinary5591.numericCaps 14 where
  ordinary q hq := by
    interval_cases q
    · exact ordinary_of_joint R ell hex 0
    · exact ordinary_of_joint R ell hex 1
    · exact ordinary_of_joint R ell hex 2
    · exact ordinary_of_joint R ell hex 3
  source := source_of_exclusion R ell 19 hex.source
  double := double_of_exclusion R ell 17 hex.dominator
  triple := perfect_of_exclusion R ell 15 3 hex.perfect
  markedOne q hqlo hqhi := by
    interval_cases q
    · exact marked_of_joint R ell hex 0
    · exact marked_of_joint R ell hex 1
    · exact marked_of_joint R ell hex 2
  markedTwo q hqlo hqhi := by
    interval_cases q
    · exact marked_of_joint R ell hex 4
    · exact marked_of_joint R ell hex 5
  zeroThree := marked_of_joint R ell hex 6
  zeroFour := marked_of_joint R ell hex 7
  zeroFive := marked_of_joint R ell hex 8
  zeroSix := marked_of_joint R ell hex 9
  zeroSeven := marked_of_joint R ell hex 11





end
end Sensitivity5591BoolCaps




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : Fintype.{0} V] [inst_1 : DecidableEq.{1} V] (R : V → V → Prop)
  (ell : Prod.{0, 0} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hex : @Sensitivity213981Formal.Sensitivity5591Labeling.Caps.JointExclusions.{0} V inst inst_1 R ell),
  @Sensitivity213981Formal.ThreeBoundRankNumeric.CapsSound V inst inst_1 R
    (@Sensitivity213981Formal.Sensitivity10007BoolCaps.boolLabel V ell)
    Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) := @Sensitivity213981Formal.Sensitivity5591BoolCaps.caps_sound
