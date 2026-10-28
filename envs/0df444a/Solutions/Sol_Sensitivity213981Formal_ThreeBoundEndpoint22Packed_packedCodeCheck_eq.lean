-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.packedCodeCheck_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:58:17.658698+00:00
-- url     : https://prove2.me/submissions/b20f9076-2f18-4905-865b-081a25e208a0

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedPrepared
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankConvertedPreparation
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
import Mathlib.Data.Prod.Lex
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


namespace Sensitivity213981Formal
section
/- Each static record needs only four converted caps per external-arc count.
The q-specific greedy increments are then computed from these small arrays. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps interval )
open ThreeBoundRankNumeric

















theorem readNegative_preparedFromConverted (q external : ℕ) (values : ConvertedValues)
    (e : Fin (external+1)) (k : Fin (q+1)) :
    readNegative (preparedFromConverted q external values) e.val k.val=
      convertedNegative values q e.val k.val := by
  simp [readNegative,preparedFromConverted,Array.getD,e.isLt,k.isLt]













end ThreeBoundRankCached




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Direct four-tier arithmetic avoids constructing nested temporary arrays. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundNumeric (maximum interval)
open ThreeBoundRankNumeric ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records





theorem packedNegativeCost_eq (q : Fin 4) (code external : ℕ) (e : Fin (external+1))
    (cv : ConvertedValues) (values : CostValues)
    (hc : ∀ k : Fin 4, readConverted cv e.val k.val=packedCap code e.val k.val) :
    packedNegativeCost q.val code e.val values=
      ((List.range (q.val+1)).map fun k =>
        readNegative (preparedFromConverted q.val external cv) e.val k*values.negative.getD k 0).sum := by
  have hs : ((List.range (q.val+1)).map fun k =>
      readNegative (preparedFromConverted q.val external cv) e.val k*values.negative.getD k 0)=
      ((List.range (q.val+1)).map fun k => convertedNegative cv q.val e.val k*values.negative.getD k 0) := by
    apply List.map_congr_left
    intro k hk
    rw [readNegative_preparedFromConverted q.val external cv e ⟨k,List.mem_range.mp hk⟩]
  rw [hs]
  have h0:=hc 0
  have h1:=hc 1
  have h2:=hc 2
  have h3:=hc 3
  change readConverted cv e.val 0=packedCap code e.val 0 at h0
  change readConverted cv e.val 1=packedCap code e.val 1 at h1
  change readConverted cv e.val 2=packedCap code e.val 2 at h2
  change readConverted cv e.val 3=packedCap code e.val 3 at h3
  fin_cases q <;>
    simp [packedNegativeCost,convertedNegative,convertedSuffix,interval,List.range_succ,
      h0,h1,h2,h3,min_assoc,min_left_comm,min_comm,Nat.add_assoc]



theorem packedVariableCost_eq (q : Fin 4) (code external : ℕ) (e : Fin (external+1))
    (cv : ConvertedValues) (values : CostValues)
    (hc : ∀ k : Fin 4, readConverted cv e.val k.val=packedCap code e.val k.val) :
    packedVariableCost q.val code values external e.val=
      variablePreparedCost q.val (preparedFromConverted q.val external cv) values external e.val := by
  simp only [packedVariableCost,variablePreparedCost,packedNegativeCost_eq q code external e cv values hc]

theorem convertedValues_read (key : ℕ) (e : Fin (staticRow key 11+1)) (k : Fin 4) :
    readConverted (convertedValues key) e.val k.val=packedCap (convertedCodes.get key) e.val k.val := by
  fin_cases k <;>
    simp [readConverted,convertedValues,packedCap,Array.getD,e.isLt]

theorem convertedValues_feasible (key : ℕ) (q : Fin 4) :
    (convertedValues key).feasible.getD q.val false=true := by
  fin_cases q <;> norm_num [convertedValues,feasibleCodes,ThreeBoundNumeric.NatTable.get,Array.getD]
  all_goals decide +kernel



theorem packedCodeCheck_eq (q : Fin 4) (key : ℕ) (values : CostValues) (bound code : ℕ)
    (he : codeRecord code 11=staticRow key 11) :
    packedCodeCheck q.val (convertedCodes.get key) values bound code=
      fusedCodePreparedCheck q.val (prepared keyCodes.get convertedValues q.val key) values bound code := by
  have hf : (prepared keyCodes.get convertedValues q.val key).feasible=true :=
    convertedValues_feasible key q
  have hm : ((List.range (codeRecord code 11+1)).map fun e =>
      packedVariableCost q.val (convertedCodes.get key) values (codeRecord code 11) e)=
      ((List.range (codeRecord code 11+1)).map fun e =>
        variablePreparedCost q.val (prepared keyCodes.get convertedValues q.val key)
          values (codeRecord code 11) e) := by
    apply List.map_congr_left
    intro e hem
    have hlt : e< staticRow key 11+1 := by simpa only [he] using List.mem_range.mp hem
    have hc:=packedVariableCost_eq q (convertedCodes.get key) (staticRow key 11)
      ⟨e,hlt⟩ (convertedValues key) values (convertedValues_read key ⟨e,hlt⟩)
    simpa only [he,prepared,staticRow] using hc
  simp only [packedCodeCheck,fusedCodePreparedCheck,hf,if_true,hm]

end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (q : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (key : Nat)
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound code : Nat)
  (he :
    @Eq.{1} Nat
      (Sensitivity213981Formal.ThreeBoundEndpoint22Records.codeRecord code
        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
      (Sensitivity213981Formal.ThreeBoundEndpoint22Records.staticRow key
        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))),
  @Eq.{1} Bool
    (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.packedCodeCheck
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
      (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedCodes key)
      values bound code)
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
      (Sensitivity213981Formal.ThreeBoundRankAnnotated.prepared
        (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
          Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
        Sensitivity213981Formal.ThreeBoundEndpoint22Records.convertedValues
        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q) key)
      values bound code) := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.packedCodeCheck_eq
