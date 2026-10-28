-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strictP_basic
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:59:32.268326+00:00
-- url     : https://prove2.me/submissions/c5b3814c-4505-4173-b468-776cc4657449

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_same_row_up_conditional_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictOutBits_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_parent_up_cover


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















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _













theorem targetBits_card_le (F : L → (I → Bool) → Bool) (ti tj : L)
    (x : ((V × Bool) × I) → Bool) (v : V) (b : ℕ)
    (hb : BBound F ti tj b) (hstrong : ∀ c : Bool, F tj (child x v c) = true) :
    (targetBits F ti x v).card ≤  2*b := by
  calc
    (targetBits F ti x v).card ≤ 
        (flipsTo (F ti) false (child x v false)).card +
        (flipsTo (F ti) false (child x v true)).card := by
      simpa only [targetBits, card_liftBits] using Finset.card_union_le
        (liftBits v false (flipsTo (F ti) false (child x v false)))
        (liftBits v true (flipsTo (F ti) false (child x v true)))
    _ ≤  b+b := Nat.add_le_add (hb _ (hstrong false)) (hb _ (hstrong true))
    _ = 2*b := by omega











end
end ThreeBoundPositive






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩































































end
end ThreeBoundConditional




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Refined strict conditional positive transfer, including source-labeled cap. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]


























/-- First exact strict-P improvement (separate same-row and cross repairs). -/
theorem strictP_basic (S : Stage L I V) (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (tj tk tl gj gk gl : L) (htkl : tk ≤  tl) (hglgk : gl ≤  gk)
    (hgjtl : gj ≤  tl) (hgltj : gl ≤  tj) (hgltl : gl ≤  tl)
    (cap b a p m : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (hb : BBound F gl tj b) (ha : ABound F gj tl a)
    (hp : PBound F tj tk tl p) (hm : MBound F gl gk gj m)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj 0 x=true)
    (hxk : ordinaryParent S F tk gk 0 x=false) :
    (flipsTo (ordinaryParent S F tl gl 0) true x).card ≤  2*b+cap*a+max p m := by
  obtain ⟨v,hvj⟩ := (ordinary_parent_true S F tj gj 0 x).1 hxj
  have hvk : ¬ordinaryRow S F tk gk 0 x v := by
    intro h
    have hh := (ordinary_parent_true S F tk gk 0 x).2 ⟨v,h⟩
    rw [hxk] at hh
    contradiction
  calc
    _ ≤  (strictOutBits S F tl gl x v ∪ (targetBits F gl x v ∪
      flipsTo (ordinaryRowBool S F tl gl 0 v) true x)).card :=
      Finset.card_le_card (strict_parent_up_cover S hT F hF tj gj tl gl hgjtl hgltj x v hvj)
    _ ≤  (strictOutBits S F tl gl x v).card + ((targetBits F gl x v).card +
      (flipsTo (ordinaryRowBool S F tl gl 0 v) true x).card) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ ≤  cap*a+(2*b+max p m) := Nat.add_le_add
      (strictOutBits_card S F hF tj gj tl gl hgjtl hgltl x v hvj cap a hcap ha)
      (Nat.add_le_add (targetBits_card_le F gl tj x v b hb hvj.1)
        (same_row_up_conditional_card S F hF tj tk tl gj gk gl htkl hglgk x v hvj hvk p m hp hm))
    _ = _ := by omega










end
end ThreeBoundConditional




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (hT :
    @Sensitivity213981Formal.TournamentHighRows.IsTournament V
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S))
  (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (tj tk tl gj gk gl : L)
  (htkl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (hglgk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl gk)
  (hgjtl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj tl)
  (hgltj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl tj)
  (hgltl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl tl)
  (cap b a p m : Nat)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cap
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tj b)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj tl a)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F tj tk tl p)
  (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl gk gj m)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hxj :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tj gj
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
      Bool.true)
  (hxk :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tk gk
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
      Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tl gl
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Bool.true x))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) cap a))
      (@Max.max.{0} Nat Nat.instMax p m)) := @Sensitivity213981Formal.ThreeBoundConditional.strictP_basic
