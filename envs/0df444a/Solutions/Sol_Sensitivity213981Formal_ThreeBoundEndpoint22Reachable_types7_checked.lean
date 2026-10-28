-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.types7_checked
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:37:05.511166+00:00
-- url     : https://prove2.me/submissions/ce64b625-dae7-4d2c-ad80-65d8bd16c225

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks155
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks156
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks157
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks158
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks159
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks160
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks161
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks162
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks163
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks164
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks165
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks166
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks167
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks168
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks169
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks170
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks171
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks172
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks173
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks174
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks175
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks176
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks177
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks178
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks179
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks180
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks181
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks182
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks183
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks184
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks185
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks186
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks187
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks188
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks189
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks190
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks191
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks192
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks193
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedReachableSearch
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_0
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_120
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_160
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_200
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_240
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_280
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_320
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_360
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_40
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_400
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_440
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_480
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_520
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_560
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_600
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_640
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_680
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Reachable_covered7_80


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


















theorem types7_checked : Covers tree types7 := by
  have last : Covers tree (types7.drop 720) := covers_nil tree
  have h680 := covers_drop_step tree types7 680 40 covered7_680 last
  have h640 := covers_drop_step tree types7 640 40 covered7_640 h680
  have h600 := covers_drop_step tree types7 600 40 covered7_600 h640
  have h560 := covers_drop_step tree types7 560 40 covered7_560 h600
  have h520 := covers_drop_step tree types7 520 40 covered7_520 h560
  have h480 := covers_drop_step tree types7 480 40 covered7_480 h520
  have h440 := covers_drop_step tree types7 440 40 covered7_440 h480
  have h400 := covers_drop_step tree types7 400 40 covered7_400 h440
  have h360 := covers_drop_step tree types7 360 40 covered7_360 h400
  have h320 := covers_drop_step tree types7 320 40 covered7_320 h360
  have h280 := covers_drop_step tree types7 280 40 covered7_280 h320
  have h240 := covers_drop_step tree types7 240 40 covered7_240 h280
  have h200 := covers_drop_step tree types7 200 40 covered7_200 h240
  have h160 := covers_drop_step tree types7 160 40 covered7_160 h200
  have h120 := covers_drop_step tree types7 120 40 covered7_120 h160
  have h80 := covers_drop_step tree types7 80 40 covered7_80 h120
  have h40 := covers_drop_step tree types7 40 40 covered7_40 h80
  have h0 := covers_drop_step tree types7 0 40 covered7_0 h40
  exact h0
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
Sensitivity213981Formal.ThreeBoundRelaxedReachable.Covers Sensitivity213981Formal.ThreeBoundEndpoint22Packed.tree
  Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7 := @Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.types7_checked
