-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.closure_complete
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T23:57:16.519292+00:00
-- url     : https://prove2.me/submissions/bc6cc9fb-b348-4d00-9765-5d13ca5ce14a

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22Assembly
import Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData0
import Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData1
import Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData2
import Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData3
import Definitions.Def_Sensitivity213981Formal_FlatProfiles
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_ClosureCertificate_nodes_sound


namespace Sensitivity213981Formal
section
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]

























theorem sem_mono (F : Fin n → (I → Bool) → Bool) (c : Coord n) (a b : ℕ)
    (hab : a ≤  b) (ha : Sem F c a) : Sem F c b := by
  cases c with
  | a i j => exact fun hij x hx => (ha hij x hx).trans hab
  | b i j => exact fun hij x hx => (ha hij x hx).trans hab
  | m i j => exact fun hij hn x hx hy => (ha hij hn x hx hy).trans hab
  | p j l => exact fun hjl x hx hy => (ha hjl x hx hy).trans hab
  | d i j l => exact fun hij hjl x hx hy => (ha hij hjl x hx hy).trans hab













































end
end ThreeBoundFullProfile




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile






























theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤  k ∧ k <  b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩











end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Compressed numerical profile layout and a complete coordinate checker.
The interpretation is always the named semantic A/B/M/P/D coordinate. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile







theorem mem_coords {n : ℕ} (c : Coord n) : c ∈ coords n := by
  cases c with
  | a i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | b i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | m i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | p i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | d i j l =>
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,List.mem_map.mpr ⟨l,List.mem_finRange l,rfl⟩⟩⟩



theorem mem_validCoords {n : ℕ} (c : Coord n) : c ∈ validCoords n ↔ valid c := by
  simp only [validCoords,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun h=>h.2, fun h=>⟨mem_coords c,h⟩⟩





















theorem sem_of_not_valid {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (c : Coord n) (v : ℕ) (h : ¬valid c) :
    Sem F c v := by
  cases c with
  | a i j => exact fun hij => False.elim (h hij)
  | b i j => exact fun hij => False.elim (h hij)
  | m i j => exact fun hij hn => False.elim (h ⟨hij,hn⟩)
  | p j l => exact fun hjl => False.elim (h hjl)
  | d i j l => exact fun hij hjl => False.elim (h ⟨hij,hjl⟩)





end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile

variable {n : ℕ}





























theorem checkNodes_sound {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input : Profile n) (nodes : ℕ → Node n) (count c : ℕ)
    (hi : Upper F (scale c input))
    (hc : checkNodes input nodes count = true) :
    ∀ k, k< count → Sem F (nodes k).coord (c*(nodes k).value) :=
  nodes_sound F hF input nodes count c hi (fun k hk=>
    List.all_eq_true.mp hc k (List.mem_range.mpr hk))



theorem checkInterval_sound (p : ℕ → Bool) (a b : ℕ)
    (h : checkInterval p a b = true) (k : ℕ) (ha : a≤ k) (hb : k< b) : p k=true :=
  List.all_eq_true.mp h k (mem_interval.mpr ⟨ha,hb⟩)









theorem checked_closure {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input output : Profile n) (nodes : ℕ → Node n) (count : ℕ)
    (outIndex : Coord n → ℕ) (c : ℕ)
    (hi : Upper F (scale c input))
    (hn : checkNodes input nodes count = true)
    (ho : checkOutput nodes count outIndex output = true) :
    Upper F (scale c output) := by
  intro coord
  by_cases hc : valid coord
  · have hcheck := List.all_eq_true.mp ho coord ((mem_validCoords coord).mpr hc)
    have hout : outIndex coord< count ∧ (nodes (outIndex coord)).coord=coord ∧
        (nodes (outIndex coord)).value≤ output coord := of_decide_eq_true hcheck
    obtain ⟨hlt,heq,hle⟩ := hout
    have hs := checkNodes_sound F hF input nodes count c hi hn (outIndex coord) hlt
    rw [heq] at hs
    exact sem_mono F coord _ _ (Nat.mul_le_mul_left c hle) hs
  · exact sem_of_not_valid F coord _ hc

end ThreeBoundNumeric.ClosureCertificate



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ClosureCertificate

theorem new_nodes_checked0:
    checkInterval (checkNode rawProfile0 nodes0) 2739 nodeCount0=true:=by decide +kernel

theorem nodes_pointwise_checked0 (k:ℕ)(hk:k< nodeCount0):
    checkNode rawProfile0 nodes0 k=true:=by
  by_cases hbase:k< 2739
  · simp [checkNode,nodes0,hbase]
  · exact checkInterval_sound _ _ _ new_nodes_checked0 k (by omega) hk

theorem output_checked0:
    checkOutput nodes0 nodeCount0 outputIndex0 profile1=true:=by decide +kernel

theorem closure0_sound {I:Type}[Fintype I]
    (F:Fin 22→(I→Bool)→Bool)(hF:Nested F)(c:ℕ)
    (hi:Upper F (scale c rawProfile0)):Upper F (scale c profile1):=by
  apply checked_closure F hF rawProfile0 profile1 nodes0 nodeCount0 outputIndex0 c hi
  · exact List.all_eq_true.mpr (fun k hk=>nodes_pointwise_checked0 k (List.mem_range.mp hk))
  · exact output_checked0
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ClosureCertificate

theorem new_nodes_checked1:
    checkInterval (checkNode rawProfile1 nodes1) 2739 nodeCount1=true:=by decide +kernel

theorem nodes_pointwise_checked1 (k:ℕ)(hk:k< nodeCount1):
    checkNode rawProfile1 nodes1 k=true:=by
  by_cases hbase:k< 2739
  · simp [checkNode,nodes1,hbase]
  · exact checkInterval_sound _ _ _ new_nodes_checked1 k (by omega) hk

theorem output_checked1:
    checkOutput nodes1 nodeCount1 outputIndex1 profile2=true:=by decide +kernel

theorem closure1_sound {I:Type}[Fintype I]
    (F:Fin 22→(I→Bool)→Bool)(hF:Nested F)(c:ℕ)
    (hi:Upper F (scale c rawProfile1)):Upper F (scale c profile2):=by
  apply checked_closure F hF rawProfile1 profile2 nodes1 nodeCount1 outputIndex1 c hi
  · exact List.all_eq_true.mpr (fun k hk=>nodes_pointwise_checked1 k (List.mem_range.mp hk))
  · exact output_checked1
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ClosureCertificate

theorem new_nodes_checked2:
    checkInterval (checkNode rawProfile2 nodes2) 2739 nodeCount2=true:=by decide +kernel

theorem nodes_pointwise_checked2 (k:ℕ)(hk:k< nodeCount2):
    checkNode rawProfile2 nodes2 k=true:=by
  by_cases hbase:k< 2739
  · simp [checkNode,nodes2,hbase]
  · exact checkInterval_sound _ _ _ new_nodes_checked2 k (by omega) hk

theorem output_checked2:
    checkOutput nodes2 nodeCount2 outputIndex2 profile3=true:=by decide +kernel

theorem closure2_sound {I:Type}[Fintype I]
    (F:Fin 22→(I→Bool)→Bool)(hF:Nested F)(c:ℕ)
    (hi:Upper F (scale c rawProfile2)):Upper F (scale c profile3):=by
  apply checked_closure F hF rawProfile2 profile3 nodes2 nodeCount2 outputIndex2 c hi
  · exact List.all_eq_true.mpr (fun k hk=>nodes_pointwise_checked2 k (List.mem_range.mp hk))
  · exact output_checked2
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ClosureCertificate

theorem new_nodes_checked3:
    checkInterval (checkNode rawProfile3 nodes3) 2739 nodeCount3=true:=by decide +kernel

theorem nodes_pointwise_checked3 (k:ℕ)(hk:k< nodeCount3):
    checkNode rawProfile3 nodes3 k=true:=by
  by_cases hbase:k< 2739
  · simp [checkNode,nodes3,hbase]
  · exact checkInterval_sound _ _ _ new_nodes_checked3 k (by omega) hk

theorem output_checked3:
    checkOutput nodes3 nodeCount3 outputIndex3 profile4=true:=by decide +kernel

theorem closure3_sound {I:Type}[Fintype I]
    (F:Fin 22→(I→Bool)→Bool)(hF:Nested F)(c:ℕ)
    (hi:Upper F (scale c rawProfile3)):Upper F (scale c profile4):=by
  apply checked_closure F hF rawProfile3 profile4 nodes3 nodeCount3 outputIndex3 c hi
  · exact List.all_eq_true.mpr (fun k hk=>nodes_pointwise_checked3 k (List.mem_range.mp hk))
  · exact output_checked3
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
namespace ThreeBoundMinmaxNumeric.Endpoint22

theorem closure_complete : ClosureBounds := by
  intro p I _ F hF c h
  fin_cases p
  · exact closure0_sound F hF c h
  · exact closure1_sound F hF c h
  · exact closure2_sound F hF c h
  · exact closure3_sound F hF c h
end ThreeBoundMinmaxNumeric.Endpoint22


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.ClosureBounds := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.closure_complete
