-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxCandidates.repair_cover
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:15:27.94726+00:00
-- url     : https://prove2.me/submissions/6e49bfd3-bee7-4965-a2b6-4d297c856069

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRepair_failed_decrease


namespace Sensitivity213981Formal
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]



















theorem child_flip_same (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (i : I) :
    child (_root_.OAI.Paper320.flip x {((v,c),i)}) v c = _root_.OAI.Paper320.flip (child x v c) {i} := by
  classical
  funext a
  simp [child, _root_.OAI.Paper320.flip]

theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (v w : V) (c e : Bool) (i : I) (h : (w,e) ≠ (v,c)) :
    child (_root_.OAI.Paper320.flip x {((v,c),i)}) w e = child x w e := by
  classical
  funext a
  have hh : ((w,e),a) ≠ ((v,c),i) := by
    intro he
    exact h (congrArg Prod.fst he)
  simp [child, _root_.OAI.Paper320.flip, hh]

























/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Actual parent one-bit repairs are covered by the graded target/guard candidates.
This connects the concrete Boolean functions to the finite q2 type analysis.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundRepair
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
noncomputable section

variable {L I V : Type} [Fintype V]

theorem failed_flip_mem_other (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w z : V) (c : Bool) (a : I)
    (h : (z, S.label v z) ≠ (w,c)) :
    z ∈ failed S F l (_root_.OAI.Paper320.flip x {((w,c),a)}) v ↔ z ∈ failed S F l x v := by
  simp only [failed, Finset.mem_filter, Finset.mem_univ, true_and,
    child_flip_other x w z c (S.label v z) a h]

theorem failed_flip_own (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (a : I) :
    failed S F l (_root_.OAI.Paper320.flip x {((v,c),a)}) v = failed S F l x v := by
  ext z
  by_cases hz : z = v
  · subst z
    simp [failed, S.loopless v]
  · exact failed_flip_mem_other S F l x v v z c a
      (fun h => hz (congrArg Prod.fst h))





theorem parent_false_rejects_row (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (hx : parent S F l x = false)
    (v : V) (hq : (failed S F l x v).card ≤  S.tolerance l) :
    S.target l (failed S F l x v).card (child x v false) (child x v true) = false := by
  cases ht : S.target l (failed S F l x v).card (child x v false) (child x v true) with
  | false => rfl
  | true =>
      have hon := (parent_true_iff S F l x).2 ⟨v,hq,ht⟩
      rw [hx] at hon
      contradiction

variable [Preorder L]





end
end ThreeBoundRepair





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Shared actual-predicate interface for symmetric min/max transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]

theorem mm_comm (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=mm F t u y x := by
  simp only [mm,Bool.and_comm,Bool.or_comm]

theorem mm_mono (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti ui tj uj : L) (ht : ti ≤  tj) (hu : ui ≤  uj) (x y : I → Bool)
    (h : mm F tj uj x y=true) : mm F ti ui x y=true := by
  rw [mm_true] at h ⊢
  exact ⟨hF _ _ ht _ h.1,hF _ _ ht _ h.2.1,
    h.2.2.elim (fun hh => Or.inl (hF _ _ hu _ hh)) (fun hh => Or.inr (hF _ _ hu _ hh))⟩



theorem parent_true_of_count (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (l : L) (t u : ℕ → L) (ht : Monotone t) (hu : Monotone u)
    (hdef : ∀ d a b, S.target l d a b=mm F (t d) (u d) a b)
    (x : ((V × Bool) × I) → Bool) (w : V) (d : ℕ)
    (hd : d ≤  S.tolerance l) (hc : (failed S F l x w).card ≤  d)
    (hm : mm F (t d) (u d) (child x w false) (child x w true)=true) : parent S F l x=true := by
  apply (parent_true_iff S F l x).2
  refine ⟨w,hc.trans hd,?_⟩
  rw [hdef]
  exact mm_mono F hF _ _ _ _ (ht hc) (hu hc) _ _ hm







end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Every actual min/max parent repair is covered by an exact target repair
or the removal of one selected failed guard. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem repair_cover (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) (a : I)
    (hoff : parent S F j x=false) (hon : parent S F j (_root_.OAI.Paper320.flip x {((w,c),a)})=true) :
    (∃ b, TargetCandidate S F P.strongLower P.strongUpper j x w b ∧
      a ∈ upPart F (P.strongLower b) (P.strongUpper b) (child x w) c) ∨
    (∃ v b, GuardCandidate S F P.strongLower P.strongUpper j x v b ∧
      S.Adj v w ∧ S.label v w=c ∧ F (S.guard j) (child x w c)=true ∧
        a ∈ flipsTo (F (S.guard j)) false (child x w c)) := by
  obtain ⟨v,hq,hwin⟩ := (parent_true_iff S F j _).1 hon
  by_cases hw : w=v
  · subst w
    rw [failed_flip_own] at hq hwin
    let b := (failed S F j x v).card
    have hf := parent_false_rejects_row S F j x hoff v hq
    rw [P.strongDef] at hf hwin
    have ha : a ∈ upPart F (P.strongLower b) (P.strongUpper b) (child x v) c := by
      cases c
      · rw [child_flip_same,child_flip_other x v v false true a (by simp)] at hwin
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwin⟩
      · rw [child_flip_other x v v true false a (by simp),child_flip_same,mm_comm] at hwin
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwin⟩
    have hp : F (P.strongLower b) (child x v false)=true ∨
        F (P.strongLower b) (child x v true)=true := by
      have hh := ((mm_true F _ _ _ _).1 (Finset.mem_filter.mp ha).2).2.1
      cases c
      · exact Or.inr hh
      · exact Or.inl hh
    exact Or.inl ⟨b,⟨hq,rfl,hf,hp⟩,ha⟩
  · have hchild : ∀ e : Bool, child (_root_.OAI.Paper320.flip x {((w,c),a)}) v e=child x v e := by
      intro e
      exact child_flip_other x w v c e a (fun h => hw (congrArg Prod.fst h).symm)
    rw [hchild false,hchild true,P.strongDef] at hwin
    let b := (failed S F j (_root_.OAI.Paper320.flip x {((w,c),a)}) v).card
    have hdec : b <  (failed S F j x v).card := by
      by_contra hn
      have hc : (failed S F j x v).card ≤  b := Nat.le_of_not_gt hn
      have he := parent_true_of_count S F hF j P.strongLower P.strongUpper
        P.strongLowerMono P.strongUpperMono P.strongDef x v b hq hc hwin
      rw [hoff] at he
      contradiction
    obtain ⟨hR,hl,hbefore,hafter,hcount⟩ := failed_decrease S F j x v w c a hdec
    exact Or.inr ⟨v,b,⟨hq,hcount,hwin⟩,hR,hl,hbefore,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hafter⟩⟩



end
end ThreeBoundMinmaxCandidates




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (i j : L)
  (P :
    @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData L I V
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      S F i j)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (c : Bool) (a : I)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F j x) Bool.false)
  (hon :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F j
        (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
          (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
            (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
            (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a))))
      Bool.true),
  Or
    (@Exists.{1} Nat fun (b : Nat) =>
      And
        (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.TargetCandidate L I V inst_2 S F
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
            S F i j P)
          (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
            S F i j P)
          j x w b)
        (@Membership.mem.{0, 0} I (Finset.{0} I)
          (@SetLike.instMembership.{0, 0} (Finset.{0} I) I (@Finset.instSetLike.{0} I))
          (@Sensitivity213981Formal.ThreeBoundMinmaxHeads.upPart L I inst_1 F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P b)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P b)
            (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w) c)
          a))
    (@Exists.{1} V fun (v : V) =>
      @Exists.{1} Nat fun (b : Nat) =>
        And
          (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.GuardCandidate L I V inst_2 S F
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongLower L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.PairData.strongUpper L I V
              (@PartialOrder.toPreorder.{0} L
                (@SemilatticeInf.toPartialOrder.{0} L
                  (@Lattice.toSemilatticeInf.{0} L
                    (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
              S F i j P)
            j x v b)
          (And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
            (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
              (And
                (@Eq.{1} Bool
                  (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
                    (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c))
                  Bool.true)
                (@Membership.mem.{0, 0} I (Finset.{0} I)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} I) I (@Finset.instSetLike.{0} I))
                  (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1
                    (F (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)) Bool.false
                    (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c))
                  a))))) := @Sensitivity213981Formal.ThreeBoundMinmaxCandidates.repair_cover
