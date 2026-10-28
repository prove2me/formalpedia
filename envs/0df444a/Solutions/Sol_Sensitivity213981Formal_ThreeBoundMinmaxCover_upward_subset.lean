-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxCover.upward_subset
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:23:50.756928+00:00
-- url     : https://prove2.me/submissions/017c789d-c7df-4416-bcd5-2959d8ff3f46

import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_HeadCosts
import Definitions.Def_Sensitivity213981Formal_MinmaxGlobalCover
import Definitions.Def_Sensitivity213981Formal_MinmaxHeadLocal
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCandidates_negative_guard_false
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxCandidates_repair_cover
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_mem_liftBits


namespace Sensitivity213981Formal
section
/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]











theorem mem_hits (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) (c : Bool) :
    c ∈ hits R ell G w ↔ ∃ v ∈ G, R v w ∧ ell v w = c := by
  simp only [hits, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v,⟨hv,hR⟩,hc⟩
    exact ⟨v,hv,hR,hc⟩
  · rintro ⟨v,hv,hR,hc⟩
    exact ⟨v,⟨hv,hR⟩,hc⟩



















variable {L : Type} [Preorder L]













end
end ThreeBoundAccounting




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual conditional boundary costs at one two-child head. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundHeadCharge
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





@[simp] theorem mem_headBits (v w : V) (s : Bool → Finset I) (c : Bool) (a : I) :
    ((w,c),a) ∈ headBits v s ↔ w = v ∧ a ∈ s c := by
  cases c <;> simp [headBits,mem_liftBits]





























end
end ThreeBoundHeadCharge





end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Shared actual-predicate interface for symmetric min/max transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]



theorem mm_true (F : L → (I → Bool) → Bool) (t u : L) (x y : I → Bool) :
    mm F t u x y=true ↔ F t x=true ∧ F t y=true ∧ (F u x=true ∨ F u y=true) := by
  simp only [mm,Bool.and_eq_true,Bool.or_eq_true,and_assoc]















end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual local upward and two-hit min/max costs. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxHeads
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



theorem upPart_subset_lower (F : L → (I → Bool) → Bool) (t u : L)
    (x : Bool → I → Bool) (c : Bool) : upPart F t u x c ⊆ flipsTo (F t) true (x c) := by
  intro a ha
  have hh := (Finset.mem_filter.mp ha).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((mm_true F t u _ _).1 hh).1⟩













end
end ThreeBoundMinmaxHeads




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Deduplicated actual repair sets for the min/max construction. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCover
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxHeads ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

















theorem negative_repair_missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (w : V) (b : ℕ)
    (hb : TargetCandidate S F P.strongLower P.strongUpper j x w b)
    (hw : w ∈ negativeTargets S F P.strongLower P.strongUpper j x)
    (c : Bool) (a : I) (ha : a ∈ upPart F (P.strongLower b) (P.strongUpper b) (child x w) c) :
    c=missing S F j x w := by
  have hh := ((mm_true F _ _ _ _).1 (Finset.mem_filter.mp ha).2).2.1
  have hg := hF _ _ (P.guardTarget b hb.1) _ hh
  have hf := negative_guard_false S F hF i j P x w hw
  by_contra hn
  have he : (!c)=missing S F j x w := by
    cases c <;> cases h : missing S F j x w <;> simp_all
  rw [he,hf] at hg
  contradiction

theorem upward_subset (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F j x=false) :
    flipsTo (parent S F j) true x ⊆
      negativeBits S F P.strongLower P.strongUpper j x ∪
      highBits S F P.strongLower P.strongUpper j x ∪
      externalBits S F P.strongLower P.strongUpper j x := by
  rintro ⟨⟨w,c⟩,a⟩ ha
  have hon := (Finset.mem_filter.mp ha).2
  rcases repair_cover S F hF i j P x w c a hoff hon with
    ⟨b,hcan,hpart⟩ | ⟨v,b,hcan,hR,hl,hguard,hpart⟩
  · have ht : targetAt S F P.strongLower P.strongUpper j x w := ⟨b,hcan⟩
    have hpart' : a ∈ upPart F (P.strongLower (failed S F j x w).card)
        (P.strongUpper (failed S F j x w).card) (child x w) c := by
      simpa only [hcan.2.1] using hpart
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    by_cases hh : w ∈ highHeads S F P.strongLower P.strongUpper j x
    · right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hh,(mem_headBits w w _ c a).mpr ⟨rfl,?_⟩⟩
      exact Finset.mem_union.mpr (Or.inl (by simpa only [targetParts,if_pos ht] using hpart'))
    · left
      have hn : w ∈ negativeTargets S F P.strongLower P.strongUpper j x :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hcan.1,hcan⟩,hh⟩
      have hc := negative_repair_missing S F hF i j P x w b hcan hn c a hpart
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hn,(mem_liftBits w w _ c a _).mpr ⟨rfl,hc,?_⟩⟩
      rw [← hc]
      exact upPart_subset_lower F _ _ _ c hpart'
  · have hv : v ∈ guardSources S F P.strongLower P.strongUpper j x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hcan⟩
    have hw : w ∈ failed S F j x v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,by simpa only [hl] using hguard⟩
    by_cases hh : w ∈ highHeads S F P.strongLower P.strongUpper j x
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hh,(mem_headBits w w _ c a).mpr ⟨rfl,?_⟩⟩
      have hhit : c ∈ hitChildren S F P.strongLower P.strongUpper j x w :=
        (ThreeBoundAccounting.mem_hits _ _ _ w c).mpr ⟨v,hv,hR,hl⟩
      exact Finset.mem_union.mpr (Or.inr (by simpa only [guardParts,if_pos hhit] using hpart))
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨v,hv,Finset.mem_biUnion.mpr ⟨w,Finset.mem_sdiff.mpr ⟨hw,hh⟩,?_⟩⟩
      exact (mem_liftBits w w _ c a _).mpr ⟨rfl,hl.symm,by simpa only [hl] using hpart⟩



end
end ThreeBoundMinmaxCover



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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hoff : @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F j x) Bool.false),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
      (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst_2 S F j) Bool.true x)
    (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
        @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
          (fun (a b : Prod.{0, 0} V Bool) =>
            @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
              instDecidableEqBool a b)
          (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Sensitivity213981Formal.ThreeBoundMinmaxCover.negativeBits L I V inst_1 inst_2 S F
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
          j x)
        (@Sensitivity213981Formal.ThreeBoundMinmaxCover.highBits L I V inst_1 inst_2 S F
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
          j x))
      (@Sensitivity213981Formal.ThreeBoundMinmaxCover.externalBits L I V inst_1 inst_2 S F
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
        j x)) := @Sensitivity213981Formal.ThreeBoundMinmaxCover.upward_subset
