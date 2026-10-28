-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditional.primitiveM
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:43:14.537899+00:00
-- url     : https://prove2.me/submissions/2f1db0a3-8055-4dec-b337-866fe5aa240f

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_guard_defect_down
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_ordinary_target_defect_down


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







































/-- Complete improved primitive-M transfer for actual ordinary parent functions. -/
theorem primitiveM (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
    (ti tj tk gi gj gk : L) (htij : ti ≤  tj) (htjk : tj ≤  tk)
    (hgjgi : gj ≤  gi) (hgkgj : gk ≤  gj) (qi q : ℕ) (hq : q ≤  qi)
    (degree m b a p : ℕ) (hdegree : ∀ v, (outgoing S v).card = degree)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p)
    (x : ((V × Bool) × I) → Bool)
    (hxj : ordinaryParent S F tj gj q x = true)
    (hxk : ordinaryParent S F tk gk q x = false) :
    (flipsTo (ordinaryParent S F ti gi qi) false x).card ≤ 
      max (if tj< tk then max (2*m) (m+b)+(if qi=q then (degree-q)*a else 0) else 0)
        (if gk< gj then 2*b+(if qi=q then (degree-q-1)*a+p else 0) else 0) := by
  obtain ⟨v,hv⟩ := (ordinary_parent_true S F tj gj q x).1 hxj
  by_cases hmiss : ∃ c : Bool, F tk (child x v c) = false
  · have hlt : tj< tk := by
      apply lt_of_le_of_ne htjk
      intro he
      obtain ⟨c,hc⟩ := hmiss
      have hh := hv.1 c
      rw [he,hc] at hh
      contradiction
    exact (ordinary_target_defect_down S F hF ti tj tk gi gj htij hgjgi qi q hq x v hv hmiss
      degree m b a (hdegree v) hm hb ha).trans (by rw [if_pos hlt]; exact le_max_left _ _)
  · have htk : ∀ c : Bool, F tk (child x v c) = true := by
      intro c
      cases h : F tk (child x v c) with
      | false => exact False.elim (hmiss ⟨c,h⟩)
      | true => rfl
    have hg : q <  (guardFailures S F gk x v).card := by
      by_contra hn
      have hon := (ordinary_parent_true S F tk gk q x).2 ⟨v,htk,by omega⟩
      rw [hxk] at hon
      contradiction
    have hlt : gk< gj := by
      apply lt_of_le_of_ne hgkgj
      intro he
      rw [he] at hg
      have hc := hv.2
      omega
    exact (ordinary_guard_defect_down S F hF ti tj tk gi gj gk htij hgjgi qi q hq x v hv htk hg
      degree b a p (hdegree v) hb ha hp).trans (by rw [if_pos hlt]; exact le_max_right _ _)























end
end ThreeBoundConditional




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
  (ti tj tk gi gj gk : L)
  (htij :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      ti tj)
  (htjk :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tj tk)
  (hgjgi :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gj gi)
  (hgkgj :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gk gj)
  (qi q : Nat) (hq : @LE.le.{0} Nat instLENat q qi) (degree m b a p : Nat)
  (hdegree :
    ∀ (v : V),
      @Eq.{1} Nat (@Finset.card.{0} V (@Sensitivity213981Formal.ThreeBoundPositive.outgoing L I V inst_2 S v)) degree)
  (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F ti tj tk m)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F ti tk b)
  (ha : @Sensitivity213981Formal.ThreeBoundProfiles.ABound L I inst_1 F gj gi a)
  (hp : @Sensitivity213981Formal.ThreeBoundProfiles.PBound L I inst_1 F gk gj gi p)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool)
  (hxj :
    @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tj gj q x) Bool.true)
  (hxk :
    @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F tk gk q x) Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
        (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
        (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent L I V inst_2 S F ti gi qi) Bool.false x))
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
          (@Max.max.{0} Nat Nat.instMax
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m b))
          (@ite.{1} Nat (@Eq.{1} Nat qi q) (instDecidableEqNat qi q)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree q) a)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
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
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
          (@ite.{1} Nat (@Eq.{1} Nat qi q) (instDecidableEqNat qi q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) degree q)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                a)
              p)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @Sensitivity213981Formal.ThreeBoundConditional.primitiveM
