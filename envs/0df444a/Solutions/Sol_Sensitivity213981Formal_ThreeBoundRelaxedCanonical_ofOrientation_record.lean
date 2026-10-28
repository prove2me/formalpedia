-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedCanonical.ofOrientation_record
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:52:19.901368+00:00
-- url     : https://prove2.me/submissions/dfa08a9c-5f94-43f6-bdfa-4d8fa99f4eaf

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedCanonical
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Canonical sorting preserves every coordinate of the relaxed q3 record. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxedCanonical
open ThreeBoundQ3 ThreeBoundRelaxed



































theorem ofOrientation_length (ts : List Kind) (ds : List Bool) :
    (ofOrientation ts ds).length=ts.length := by simp [ofOrientation]



theorem ofOrientation_record (ts : List Kind) (ds : List Bool) :
    ThreeBoundRelaxed.record (ofOrientation ts ds)=ThreeBoundQ3.record (ts,ds) := by
  have hk : (List.finRange ts.length).map ts.get=ts := by
    simpa only [List.finRange,List.map_ofFn,Function.comp_def] using List.ofFn_get ts
  have ht (t : Kind) : ((List.finRange ts.length).filter fun v => ts.get v=t).length =
      (ts.filter fun u => u=t).length := by
    have h := congrArg (fun xs => (xs.filter fun u => decide (u=t)).length) hk
    simpa only [List.filter_map,List.length_map,Function.comp_def] using h
  have hsort := List.mergeSort_eq_insertionSort (· ≤  ·)
    ((List.finRange ts.length).map fun v => budget (ts.get v)-outCount (edges ts.length) ds v)
  dsimp only [ThreeBoundRelaxed.record,ThreeBoundQ3.record]
  simp only [ht,ofOrientation_length,ofOrientation,List.filter_map,List.map_map,
    List.length_map,List.length_finRange,Function.comp_def,ThreeBoundQ3RecordFields.incoming,← hsort]

end ThreeBoundRelaxedCanonical





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (ds : List.{0} Bool),
  @Eq.{1} (List.{0} Nat)
    (Sensitivity213981Formal.ThreeBoundRelaxed.record
      (Sensitivity213981Formal.ThreeBoundRelaxedCanonical.ofOrientation ts ds))
    (Sensitivity213981Formal.ThreeBoundQ3.record
      (@Prod.mk.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) (List.{0} Bool) ts ds)) := @Sensitivity213981Formal.ThreeBoundRelaxedCanonical.ofOrientation_record
