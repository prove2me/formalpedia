-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.candidates_markedGood
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:44:14.053705+00:00
-- url     : https://prove2.me/submissions/6aa396bd-dbd6-4476-a062-be2a4a9ef13b

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
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
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_candidate_local_charge


namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_candidateTotalCap_bound.lean -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



















































end
end ZL
end
end z8

section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)









end Tournament



















end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)





end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)







end OAI.Paper320.Tournament
namespace SensitivityQ



















end SensitivityQ
namespace SensitivitySourceZero






















end SensitivitySourceZero
end
end z32

section z38

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]













end CompactTournament
end
end z38

section z39

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset ZL
variable {V : Type*} [Fintype V] [DecidableEq V]



end CompactTournament
end
end z39

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}











theorem candidates_markedGood (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤  t)
    (q B : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A M P : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x)
    (hP : P ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide))
    (hdis : Disjoint A M)
    (hB : (∑ y ∈ M, (ZL.mismatch T.Adj
      (fun e => label e.1 e.2) A (missingWitness F t x (by decide)) y).card) ≤  B) :
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      A M P q B (missingWitness F t x (by decide)) := by
  refine ⟨?_,?_,hB⟩
  · intro i hi
    exact (candidate_local_charge T label F hF t g hgt q x A M hA hM hdis i).trans
      (Finset.mem_filter.mp (hA hi)).2.2
  · intro i hi
    have hcharge := candidate_local_charge T label F hF t g hgt q x A M hA hM hdis i
    rw [Nat.add_comm] at hcharge
    by_cases hip : i ∈ P
    · simp only [if_pos hip, Nat.add_zero]
      exact hcharge.trans (Finset.mem_filter.mp (Finset.mem_filter.mp (hP hip)).1).2.2
    · simp only [if_neg hip]
      rcases Finset.mem_union.mp (hM hi) with hiU | hiG
      · have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hiU).1).2.2
        omega
      · have hh := (Finset.mem_filter.mp hiG).2.2
        omega





end ZT
end
end z40

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



















end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z45

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n k : Nat} {I : Type} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (t g : Fin n)
  (hgt : @LE.le.{0} (Fin n) (@instLEFin n) g t) (q B : Nat)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool)
  (A M P : Finset.{0} (Fin k))
  (hA :
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      A
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantTargets n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x))
  (hM :
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      M
      (@Union.union.{0} (Finset.{0} (Fin k)) (@Finset.instUnion.{0} (Fin k) (instDecidableEqFin k))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x
          (@of_decide_eq_true
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@id.{0}
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Bool.true)
              (@Eq.refl.{1} Bool Bool.true))))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantGuards n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x)))
  (hP :
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      P
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x
        (@of_decide_eq_true
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@id.{0}
            (@Eq.{1} Bool
              (@Decidable.decide
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              Bool.true)
            (@Eq.refl.{1} Bool Bool.true)))))
  (hdis :
    @Disjoint.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k)) (@Finset.instOrderBot.{0} (Fin k)) A M)
  (hB :
    @LE.le.{0} Nat instLENat
      (@Finset.sum.{0, 0} (Fin k) Nat Nat.instAddCommMonoid M fun (y : Fin k) =>
        @Finset.card.{0} (Fin k)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.mismatch.{0} (Fin k)
            (@Digraph.Adj.{0} (Fin k)
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T))
            (fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
              label (@Prod.fst.{0, 0} (Fin k) (Fin k) e) (@Prod.snd.{0, 0} (Fin k) (Fin k) e))
            A
            (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.missingWitness n k
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I F t x
              (@of_decide_eq_true
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@id.{0}
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    Bool.true)
                  (@Eq.refl.{1} Bool Bool.true))))
            y))
      B),
  @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedGood.{0} (Fin k) (instDecidableEqFin k)
    (@Digraph.Adj.{0} (Fin k)
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T))
    (fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
      label (@Prod.fst.{0, 0} (Fin k) (Fin k) e) (@Prod.snd.{0, 0} (Fin k) (Fin k) e))
    A M P q B
    (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.missingWitness n k
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I F t x
      (@of_decide_eq_true
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id.{0}
          (@Eq.{1} Bool
            (@Decidable.decide
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl.{1} Bool Bool.true)))) := @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.candidates_markedGood
