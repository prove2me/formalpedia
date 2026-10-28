-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxCandidates.actual_high_tags
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:15:27.422163+00:00
-- url     : https://prove2.me/submissions/3a83d0a2-17af-4301-984c-e95f4427e1b7

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxCandidates
import Definitions.Def_Sensitivity213981Formal_MinmaxPairData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundHighTypes_exists_kind


namespace Sensitivity213981Formal
section
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes













theorem ofKind_count (q d : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ b, P b → d=b) (hg : ∀ b, G b → d=b+1) (hk : OfKind q P G k) :
    d=budget q k := by
  unfold OfKind at hk
  unfold budget
  split_ifs at hk ⊢ with h1 h2
  · exact hp _ hk.1
  · have h := hg _ hk.1
    omega
  · exact hp _ hk.1









end ThreeBoundHighTypes




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















end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual geometric target and guard candidates for monotone min/max rows. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxHeads
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]



















theorem high_guards_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
    (w : V) (hw : w ∈ highHeads S F P.strongLower P.strongUpper j x) :
    ∀ c, F (S.guard j) (child x w c)=true := by
  rcases (Finset.mem_filter.mp hw).2 with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · have hh := (mm_true F _ _ _ _).1 hb.2.2
    intro c
    cases c
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.1
    · exact hF _ _ (P.guardTarget b hb.1) _ hh.2.1















end
end ThreeBoundMinmaxCandidates





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



theorem actual_high_tags (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (P : PairData S F i j)
    (x : ((V × Bool) × I) → Bool) (q : ℕ) (hq : S.tolerance j ≤  q) :
    ∃ tag : V → ThreeBoundHighTypes.Kind q,
      (∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
        ThreeBoundHighTypes.OfKind q
          (PositiveCandidate S F P.strongLower P.strongUpper j x w)
          (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w)) ∧
      (∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
        (failed S F j x w).card=ThreeBoundHighTypes.budget q (tag w)) ∧
      (∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
        ((highHeads S F P.strongLower P.strongUpper j x).filter (S.Adj w)).card ≤ 
          ThreeBoundHighTypes.budget q (tag w)) := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  have hex : ∀ w ∈ H, ∃ kind : ThreeBoundHighTypes.Kind q,
      ThreeBoundHighTypes.OfKind q (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) kind := by
    intro w hw
    exact ThreeBoundHighTypes.exists_kind q (failed S F j x w).card _ _
      (fun b hb => ⟨hb.1.1.trans hq,hb.1.2.1⟩)
      (fun b hb => ⟨hb.1.trans hq,hb.2.1⟩) (Finset.mem_filter.mp hw).2
  let tag : V → ThreeBoundHighTypes.Kind q := fun w =>
    if hw : w ∈ H then Classical.choose (hex w hw) else ⟨0,by omega⟩
  have hk : ∀ w ∈ H, ThreeBoundHighTypes.OfKind q
      (PositiveCandidate S F P.strongLower P.strongUpper j x w)
      (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w) := by
    intro w hw
    simpa only [tag,dif_pos hw] using Classical.choose_spec (hex w hw)
  have hc : ∀ w ∈ H, (failed S F j x w).card=ThreeBoundHighTypes.budget q (tag w) := by
    intro w hw
    exact ThreeBoundHighTypes.ofKind_count q (failed S F j x w).card _ _ (tag w)
      (fun b hb => hb.1.2.1) (fun b hb => hb.2.1) (hk w hw)
  refine ⟨tag,hk,hc,?_⟩
  intro w hw
  rw [← hc w hw]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hvH,hR⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,
    high_guards_true S F hF i j P x v hvH (S.label w v)⟩

end
end ThreeBoundMinmaxCandidates




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
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
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (q : Nat)
  (hq : @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance L I V S j) q),
  @Exists.{1} (V → Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
    fun (tag : V → Sensitivity213981Formal.ThreeBoundHighTypes.Kind q) =>
    And
      (∀ (w : V),
        @Membership.mem.{0, 0} V (Finset.{0} V)
            (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
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
            w →
          Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q
            (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.PositiveCandidate L I V inst_2 S F
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
              j x w)
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
              j x w)
            (tag w))
      (And
        (∀ (w : V),
          @Membership.mem.{0, 0} V (Finset.{0} V)
              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
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
              w →
            @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x w))
              (Sensitivity213981Formal.ThreeBoundHighTypes.budget q (tag w)))
        (∀ (w : V),
          @Membership.mem.{0, 0} V (Finset.{0} V)
              (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V))
              (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
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
              w →
            @LE.le.{0} Nat instLENat
              (@Finset.card.{0} V
                (@Finset.filter.{0} V (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S w)
                  (fun (a : V) =>
                    Classical.propDecidable (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S w a))
                  (@Sensitivity213981Formal.ThreeBoundMinmaxCandidates.highHeads L I V inst_2 S F
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
                    j x)))
              (Sensitivity213981Formal.ThreeBoundHighTypes.budget q (tag w)))) := @Sensitivity213981Formal.ThreeBoundMinmaxCandidates.actual_high_tags
