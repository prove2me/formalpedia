-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.strictP_refined
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:59:21.759893+00:00
-- url     : https://prove2.me/submissions/33f3fb3c-a777-463b-88e4-d578cfbba967

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictOutBits_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictP_guard_local
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictP_target_local
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



































/-- Second exact strict-P improvement, separating target and guard defects. -/
theorem strictP_refined (S : Stage L I V) (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (tj tk tl gj gk gl : L) (htjk : tj ≤  tk) (htkl : tk ≤  tl)
    (hgkgj : gk ≤  gj) (hglgk : gl ≤  gk)
    (hgjtl : gj ≤  tl) (hgltj : gl ≤  tj) (hgltl : gl ≤  tl)
    (cap a mₜ bₖ bₗ u m₉ : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (ha : ABound F gj tl a) (hmₜ : MBound F gl tj tk mₜ)
    (hbₖ : BBound F gl tk bₖ) (hbₗ : BBound F gl tl bₗ)
    (hu : DBound F gl tj tk tl u) (hm₉ : MBound F gl gk gj m₉)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj 0 x=true)
    (hxk : ordinaryParent S F tk gk 0 x=false) :
    (flipsTo (ordinaryParent S F tl gl 0) true x).card ≤ 
      max (if tj< tk then cap*a+max (max (2*mₜ) (mₜ+bₖ)) (u+bₗ) else 0)
        (if gk< gj then cap*a+max (2*bₖ) (2*bₗ+m₉) else 0) := by
  obtain ⟨v,hvj⟩ := (ordinary_parent_true S F tj gj 0 x).1 hxj
  have hvk : ¬ordinaryRow S F tk gk 0 x v := by
    intro h
    have hh := (ordinary_parent_true S F tk gk 0 x).2 ⟨v,h⟩
    rw [hxk] at hh
    contradiction
  have hout := strictOutBits_card S F hF tj gj tl gl hgjtl hgltl x v hvj cap a hcap ha
  have hcover := Finset.card_le_card (strict_parent_up_cover S hT F hF tj gj tl gl hgjtl hgltj x v hvj)
  have hsplit := hcover.trans (Finset.card_union_le _ _)
  by_cases hmiss : ∃ c : Bool, F tk (child x v c)=false
  · have hlt : tj< tk := by
      apply lt_of_le_of_ne htjk
      intro he
      obtain ⟨c,hc⟩ := hmiss
      have hh := hvj.1 c
      rw [he,hc] at hh
      contradiction
    have hh := hsplit.trans (Nat.add_le_add hout
      (strictP_target_local S F hF tj tk tl gl htkl x v hvj.1 hmiss mₜ bₖ bₗ u hmₜ hbₖ hbₗ hu))
    exact hh.trans (by rw [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c : Bool, F tk (child x v c)=true := by
      intro c
      cases h : F tk (child x v c) with
      | false => exact False.elim (hmiss ⟨c,h⟩)
      | true => rfl
    have hlt : gk< gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      apply hvk
      refine ⟨htk,?_⟩
      simpa only [he] using hvj.2
    have hh := hsplit.trans (Nat.add_le_add hout
      (strictP_guard_local S F hF tj tk tl gj gk gl hglgk x v hvj htk hvk bₖ bₗ m₉ hbₖ hbₗ hm₉))
    exact hh.trans (by rw [if_pos hlt]; exact le_max_right _ _)

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
  (htjk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tj tk)
  (htkl :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (hgkgj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
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
  (cap a mₜ bₖ bₗ u m₉ : Nat)
  (hcap :
    @Sensitivity213981Formal.ResidualCaps.DominatorCardBound V
      (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cap
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj tl a)
  (hmₜ : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl tj tk mₜ)
  (hbₖ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tk bₖ)
  (hbₗ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tl bₗ)
  (hu : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F gl tj tk tl u)
  (hm₉ : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl gk gj m₉)
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
    (@Max.max.{0} Nat Nat.instMax
      (@ite.{1} Nat
        (@LT.lt.{0} L
          (@Preorder.toLT.{0} L
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
          tj tk)
        (@LinearOrder.toDecidableLT.{0} L inst tj tk)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) cap a)
          (@Max.max.{0} Nat Nat.instMax
            (@Max.max.{0} Nat Nat.instMax
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) mₜ)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) mₜ bₖ))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u bₗ)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@ite.{1} Nat
        (@LT.lt.{0} L
          (@Preorder.toLT.{0} L
            (@PartialOrder.toPreorder.{0} L
              (@SemilatticeInf.toPartialOrder.{0} L
                (@Lattice.toSemilatticeInf.{0} L
                  (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
          gk gj)
        (@LinearOrder.toDecidableLT.{0} L inst gk gj)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) cap a)
          (@Max.max.{0} Nat Nat.instMax
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) bₖ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) bₗ)
              m₉)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @Sensitivity213981Formal.ThreeBoundConditional.strictP_refined
