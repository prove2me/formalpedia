-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.positive_union_charge
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:56:21.710819+00:00
-- url     : https://prove2.me/submissions/272d4564-1385-4287-845f-f794f23eba56

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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_sum_binary_weights


namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_ordinary_positive_of_cases.lean -/
set_option autoImplicit false
set_option Elab.async false
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
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤  Aj) (hG : Gj ≤  Gi)
  (x : ((Fin k × Fin r) × I) → Bool)







end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



























end ZT
end
end z30

section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]























end ZT
end
end z31

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

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





















end ZT
end
end z34

section z35

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
namespace ZT

theorem binary_capacity_charge (n z N J s j : ℕ)
    (hjs : j ≤  s) (hnz : n ≤  z) (hnN : n ≤  N) (hz : z ≤  N+J) :
    n*s+(z-n)*j ≤  N*s+J*j := by
  have hn : n+(N-n)=N := Nat.add_sub_of_le hnN
  have hzn : n+(z-n)=z := Nat.add_sub_of_le hnz
  have hm := Nat.mul_le_mul_left (N-n) hjs
  have htail := Nat.mul_le_mul_right j (show z-n ≤  (N-n)+J by omega)
  nlinarith

theorem positive_capacity_charge (n z E W L u δ s j : ℕ)
    (hjs : j ≤  s) (hnz : n ≤  z)
    (hnE : n+δ ≤  E) (hnW : n+δ ≤  W+u)
    (hzE : z ≤  E) (hzW : z ≤  W+2*u)
    (hWL : W+L ≤  E) (hδW : δ ≤  W) :
    n*s+(z-n)*j ≤ 
      (E-(L-u)-δ)*s+(min u (L-u)+δ)*j := by
  apply binary_capacity_charge _ _ _ _ _ _ hjs hnz
  · omega
  · omega

theorem positive_union_charge {V α : Type} [DecidableEq V] [DecidableEq α]
    (Z : Finset V) (inside costly : V → Prop)
    [DecidablePred inside] [DecidablePred costly]
    (D : V → Finset α) (E W L u δ s j : ℕ)
    (hjs : j ≤  s)
    (hZ : Z.card ≤  E) (hW : (Z.filter (fun v => ¬ inside v)).card ≤  W)
    (hL : W+L ≤  E)
    (hin : (Z.filter inside).card ≤  2*u)
    (hcost : (Z.filter fun v => inside v ∧ costly v).card ≤  u)
    (hcheap : δ ≤  (Z.filter fun v => ¬ inside v ∧ ¬ costly v).card)
    (hD : ∀ v ∈ Z, (D v).card ≤  if costly v then s else j) :
    (Z.biUnion D).card ≤  (E-(L-u)-δ)*s+(min u (L-u)+δ)*j := by
  let n := (Z.filter costly).card
  let z := Z.card
  let ni := (Z.filter fun v => inside v ∧ costly v).card
  let no := (Z.filter fun v => ¬ inside v ∧ costly v).card
  let co := (Z.filter fun v => ¬ inside v ∧ ¬ costly v).card
  let out := (Z.filter fun v => ¬ inside v).card
  have hnz : n ≤  z := Finset.card_filter_le _ _
  have hout : no+co=out := by
    simpa only [no,co,out,Finset.filter_filter,and_assoc] using
      (Finset.card_filter_add_card_filter_not (s := Z.filter fun v => ¬inside v) costly)
  have hn : ni+no=n := by
    simpa only [ni,no,n,Finset.filter_filter,and_comm] using
      (Finset.card_filter_add_card_filter_not (s := Z.filter costly) inside)
  have hsplit : (Z.filter inside).card+out=z := by
    exact Finset.card_filter_add_card_filter_not (s := Z) inside
  have hδW : δ ≤  W := by
    have hco : co ≤  out := by omega
    exact hcheap.trans (hco.trans hW)
  have hnW : n+δ ≤  W+u := by
    change ni ≤  u at hcost
    change δ ≤  co at hcheap
    change out ≤  W at hW
    omega
  have hzW : z ≤  W+2*u := by
    change out ≤  W at hW
    omega
  have hnE : n+δ ≤  E := by
    have hdis : Disjoint (Z.filter costly)
        (Z.filter fun v => ¬inside v ∧ ¬costly v) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (Finset.mem_filter.mp hw).2.2 (Finset.mem_filter.mp hv).2
    have hcard : n+co ≤  z := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    change δ ≤  co at hcheap
    omega
  have hbound : (Z.biUnion D).card ≤  n*s+(z-n)*j := by
    apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum hD).trans_eq
    exact sum_binary_weights Z costly s j
  exact hbound.trans (positive_capacity_charge n z E W L u δ s j hjs hnz hnE hnW hZ hzW hL hδW)



end ZT
end
end z35

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard










end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















end ZT
end
end z37

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

end ZT
end
end z40

section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

















end ZT
end
end z41

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

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



end ZT
end
end z58

section z59

set_option maxHeartbeats 5000000
namespace ZT









end ZT
end z59

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]











end ZT
end
end z60

section z61

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













end ZT
end
end z61

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V α : Type} [DecidableEq.{1} V] [inst : DecidableEq.{1} α] (Z : Finset.{0} V) (inside costly : V → Prop)
  [inst_1 : @DecidablePred.{1} V inside] [inst_2 : @DecidablePred.{1} V costly] (D : V → Finset.{0} α)
  (E W L u δ s j : Nat) (hjs : @LE.le.{0} Nat instLENat j s) (hZ : @LE.le.{0} Nat instLENat (@Finset.card.{0} V Z) E)
  (hW :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (v : V) => Not (inside v)) (fun (a : V) => @instDecidableNot (inside a) (inst_1 a))
          Z))
      W)
  (hL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W L) E)
  (hin :
    @LE.le.{0} Nat instLENat (@Finset.card.{0} V (@Finset.filter.{0} V inside inst_1 Z))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))
  (hcost :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (v : V) => And (inside v) (costly v))
          (fun (a : V) => @instDecidableAnd (inside a) (costly a) (inst_1 a) (inst_2 a)) Z))
      u)
  (hcheap :
    @LE.le.{0} Nat instLENat δ
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (v : V) => And (Not (inside v)) (Not (costly v)))
          (fun (a : V) =>
            @instDecidableAnd (Not (inside a)) (Not (costly a)) (@instDecidableNot (inside a) (inst_1 a))
              (@instDecidableNot (costly a) (inst_2 a)))
          Z)))
  (hD :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) Z v →
        @LE.le.{0} Nat instLENat (@Finset.card.{0} α (D v)) (@ite.{1} Nat (costly v) (inst_2 v) s j)),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} α (@Finset.biUnion.{0, 0} V α inst Z D))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) E
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L u))
          δ)
        s)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Min.min.{0} Nat instMinNat u (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L u)) δ)
        j)) := @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.positive_union_charge
