-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.types0_checked
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:56:38.870491+00:00
-- url     : https://prove2.me/submissions/bc51e58b-ea6a-4365-a44f-8673d34fb043

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks000
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedReachableSearch
import Definitions.Def_Sensitivity213981Formal_RelaxedRecordCoverage
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_Certificates_Endpoint22ReachChecks000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t0_0checked : Sensitivity213981Formal.ThreeBoundRelaxedReachable.Checked Sensitivity213981Formal.ThreeBoundEndpoint22Packed.tree
  (@List.nil.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind) := Sensitivity213981Formal.Certificates.Endpoint22ReachChecks000.r29

namespace Sensitivity213981Formal
section
/- Shared suffix bitsets retain every degree completion. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000
namespace ThreeBoundRelaxedReachable
open ThreeBoundQ3 ThreeBoundRelaxed ThreeBoundRelaxedCompiled
open ThreeBoundRelaxedPacked (Tree fastKey)























































theorem covers_nil (tree : Tree) : Covers tree [] := by intro ts ht; simp at ht

theorem covers_cons {tree : Tree} {ts : List Kind} {xs : List (List Kind)}
    (h : Checked tree ts) (ht : Covers tree xs) : Covers tree (ts::xs) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact h
  · exact ht a ha

theorem covers_drop_step (tree : Tree) (xs : List (List Kind)) (start count : ℕ)
    (hl : Covers tree ((xs.drop start).take count))
    (hr : Covers tree (xs.drop (start+count))) : Covers tree (xs.drop start) := by
  intro ts ht
  rw [← List.take_append_drop count (xs.drop start)] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hl ts ht
  · apply hr ts
    simpa only [List.drop_drop,Nat.add_comm] using ht



end ThreeBoundRelaxedReachable


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
open ThreeBoundEndpoint22Packed (tree)
open ThreeBoundEndpoint22Types
theorem covered0_0 : Covers tree ((types0.drop 0).take 1) := by
  change Covers tree [[]]
  apply covers_cons t0_0checked
  exact covers_nil tree
theorem types0_checked : Covers tree types0 := by
  have last : Covers tree (types0.drop 1) := covers_nil tree
  have h0 := covers_drop_step tree types0 0 1 covered0_0 last
  exact h0
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
Sensitivity213981Formal.ThreeBoundRelaxedReachable.Covers Sensitivity213981Formal.ThreeBoundEndpoint22Packed.tree
  Sensitivity213981Formal.ThreeBoundEndpoint22Types.types0 := @Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.types0_checked
