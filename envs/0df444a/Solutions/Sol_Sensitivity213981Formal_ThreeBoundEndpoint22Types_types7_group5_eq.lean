-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group5_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:55:38.711691+00:00
-- url     : https://prove2.me/submissions/35f8b2d1-4b56-411a-84c5-1b4b07ad044e

import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22TypeSplit
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Exact bounded Type7 group. Generated source; requires Lean checking. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Types
open ThreeBoundQ3 ThreeBoundEndpoint22TypeSplit

private theorem prefix7_5_3_3 : filteredPrefix ([5,3,3] : List Kind) (orderKey (3 : Kind)) 4 = [[5,3,3,3,3,3,7],[5,3,3,3,3,6,7],[5,3,3,3,3,7,7],[5,3,3,3,3,10,7],[5,3,3,3,6,6,7],[5,3,3,3,6,7,7],[5,3,3,3,6,10,7],[5,3,3,3,7,7,7],[5,3,3,3,10,7,7],[5,3,3,3,10,10,7],[5,3,3,6,6,6,7],[5,3,3,6,6,7,7],[5,3,3,6,6,10,7],[5,3,3,6,7,7,7],[5,3,3,6,10,7,7],[5,3,3,6,10,10,7],[5,3,3,7,7,7,7],[5,3,3,10,7,7,7],[5,3,3,10,10,7,7],[5,3,3,10,10,10,7]] := by decide +kernel

private theorem prefix7_5_3_6 : filteredPrefix ([5,3,6] : List Kind) (orderKey (6 : Kind)) 4 = [[5,3,6,6,6,6,7],[5,3,6,6,6,7,7],[5,3,6,6,6,10,7],[5,3,6,6,7,7,7],[5,3,6,6,10,7,7],[5,3,6,6,10,10,7],[5,3,6,7,7,7,7],[5,3,6,10,7,7,7],[5,3,6,10,10,7,7],[5,3,6,10,10,10,7]] := by decide +kernel

private theorem prefix7_5_3_7 : filteredPrefix ([5,3,7] : List Kind) (orderKey (7 : Kind)) 4 = [[5,3,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_5_3_10 : filteredPrefix ([5,3,10] : List Kind) (orderKey (10 : Kind)) 4 = [[5,3,10,7,7,7,7],[5,3,10,10,7,7,7],[5,3,10,10,10,7,7],[5,3,10,10,10,10,7]] := by decide +kernel

private theorem prefix7_5_5_3 : filteredPrefix ([5,5,3] : List Kind) (orderKey (3 : Kind)) 4 = [[5,5,3,3,3,7,7],[5,5,3,3,6,7,7],[5,5,3,3,7,7,7],[5,5,3,3,10,7,7],[5,5,3,6,6,7,7],[5,5,3,6,7,7,7],[5,5,3,6,10,7,7],[5,5,3,7,7,7,7],[5,5,3,10,7,7,7],[5,5,3,10,10,7,7]] := by decide +kernel

private theorem prefix7_5_5_5 : filteredPrefix ([5,5,5] : List Kind) (orderKey (5 : Kind)) 4 = [[5,5,5,3,7,7,7],[5,5,5,6,7,7,7],[5,5,5,7,7,7,7],[5,5,5,10,7,7,7]] := by decide +kernel

private theorem prefix7_5_5_6 : filteredPrefix ([5,5,6] : List Kind) (orderKey (6 : Kind)) 4 = [[5,5,6,6,6,7,7],[5,5,6,6,7,7,7],[5,5,6,6,10,7,7],[5,5,6,7,7,7,7],[5,5,6,10,7,7,7],[5,5,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_5_5_7 : filteredPrefix ([5,5,7] : List Kind) (orderKey (7 : Kind)) 4 = [[5,5,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_5_5_9 : filteredPrefix ([5,5,9] : List Kind) (orderKey (9 : Kind)) 4 = [[5,5,9,3,7,7,7],[5,5,9,6,7,7,7],[5,5,9,7,7,7,7],[5,5,9,10,7,7,7]] := by decide +kernel

private theorem prefix7_5_5_10 : filteredPrefix ([5,5,10] : List Kind) (orderKey (10 : Kind)) 4 = [[5,5,10,7,7,7,7],[5,5,10,10,7,7,7],[5,5,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_5_6_6 : filteredPrefix ([5,6,6] : List Kind) (orderKey (6 : Kind)) 4 = [[5,6,6,6,6,6,7],[5,6,6,6,6,7,7],[5,6,6,6,6,10,7],[5,6,6,6,7,7,7],[5,6,6,6,10,7,7],[5,6,6,6,10,10,7],[5,6,6,7,7,7,7],[5,6,6,10,7,7,7],[5,6,6,10,10,7,7],[5,6,6,10,10,10,7]] := by decide +kernel

private theorem prefix7_5_6_7 : filteredPrefix ([5,6,7] : List Kind) (orderKey (7 : Kind)) 4 = [[5,6,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_5_6_10 : filteredPrefix ([5,6,10] : List Kind) (orderKey (10 : Kind)) 4 = [[5,6,10,7,7,7,7],[5,6,10,10,7,7,7],[5,6,10,10,10,7,7],[5,6,10,10,10,10,7]] := by decide +kernel

private theorem prefix7_5_7_7 : filteredPrefix ([5,7,7] : List Kind) (orderKey (7 : Kind)) 4 = [[5,7,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_5_9_3 : filteredPrefix ([5,9,3] : List Kind) (orderKey (3 : Kind)) 4 = [[5,9,3,3,3,7,7],[5,9,3,3,6,7,7],[5,9,3,3,7,7,7],[5,9,3,3,10,7,7],[5,9,3,6,6,7,7],[5,9,3,6,7,7,7],[5,9,3,6,10,7,7],[5,9,3,7,7,7,7],[5,9,3,10,7,7,7],[5,9,3,10,10,7,7]] := by decide +kernel

private theorem prefix7_5_9_6 : filteredPrefix ([5,9,6] : List Kind) (orderKey (6 : Kind)) 4 = [[5,9,6,6,6,7,7],[5,9,6,6,7,7,7],[5,9,6,6,10,7,7],[5,9,6,7,7,7,7],[5,9,6,10,7,7,7],[5,9,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_5_9_7 : filteredPrefix ([5,9,7] : List Kind) (orderKey (7 : Kind)) 4 = [[5,9,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_5_9_9 : filteredPrefix ([5,9,9] : List Kind) (orderKey (9 : Kind)) 4 = [[5,9,9,3,7,7,7],[5,9,9,6,7,7,7],[5,9,9,7,7,7,7],[5,9,9,10,7,7,7]] := by decide +kernel

private theorem prefix7_5_9_10 : filteredPrefix ([5,9,10] : List Kind) (orderKey (10 : Kind)) 4 = [[5,9,10,7,7,7,7],[5,9,10,10,7,7,7],[5,9,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_5_10_7 : filteredPrefix ([5,10,7] : List Kind) (orderKey (7 : Kind)) 4 = [[5,10,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_5_10_10 : filteredPrefix ([5,10,10] : List Kind) (orderKey (10 : Kind)) 4 = [[5,10,10,7,7,7,7],[5,10,10,10,7,7,7],[5,10,10,10,10,7,7],[5,10,10,10,10,10,7]] := by decide +kernel

theorem types7_group5_eq :
    ((filteredPrefix ([5,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([5,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([5,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([5,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([5,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([5,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([5,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[5,3,3,3,3,3,7],[5,3,3,3,3,6,7],[5,3,3,3,3,7,7],[5,3,3,3,3,10,7],[5,3,3,3,6,6,7],[5,3,3,3,6,7,7],[5,3,3,3,6,10,7],[5,3,3,3,7,7,7],[5,3,3,3,10,7,7],[5,3,3,3,10,10,7],[5,3,3,6,6,6,7],[5,3,3,6,6,7,7],[5,3,3,6,6,10,7],[5,3,3,6,7,7,7],[5,3,3,6,10,7,7],[5,3,3,6,10,10,7],[5,3,3,7,7,7,7],[5,3,3,10,7,7,7],[5,3,3,10,10,7,7],[5,3,3,10,10,10,7],[5,3,6,6,6,6,7],[5,3,6,6,6,7,7],[5,3,6,6,6,10,7],[5,3,6,6,7,7,7],[5,3,6,6,10,7,7],[5,3,6,6,10,10,7],[5,3,6,7,7,7,7],[5,3,6,10,7,7,7],[5,3,6,10,10,7,7],[5,3,6,10,10,10,7],[5,3,7,7,7,7,7],[5,3,10,7,7,7,7],[5,3,10,10,7,7,7],[5,3,10,10,10,7,7],[5,3,10,10,10,10,7],[5,5,3,3,3,7,7],[5,5,3,3,6,7,7],[5,5,3,3,7,7,7],[5,5,3,3,10,7,7],[5,5,3,6,6,7,7],[5,5,3,6,7,7,7],[5,5,3,6,10,7,7],[5,5,3,7,7,7,7],[5,5,3,10,7,7,7],[5,5,3,10,10,7,7],[5,5,5,3,7,7,7],[5,5,5,6,7,7,7],[5,5,5,7,7,7,7],[5,5,5,10,7,7,7],[5,5,6,6,6,7,7],[5,5,6,6,7,7,7],[5,5,6,6,10,7,7],[5,5,6,7,7,7,7],[5,5,6,10,7,7,7],[5,5,6,10,10,7,7],[5,5,7,7,7,7,7],[5,5,9,3,7,7,7],[5,5,9,6,7,7,7],[5,5,9,7,7,7,7],[5,5,9,10,7,7,7],[5,5,10,7,7,7,7],[5,5,10,10,7,7,7],[5,5,10,10,10,7,7],[5,6,6,6,6,6,7],[5,6,6,6,6,7,7],[5,6,6,6,6,10,7],[5,6,6,6,7,7,7],[5,6,6,6,10,7,7],[5,6,6,6,10,10,7],[5,6,6,7,7,7,7],[5,6,6,10,7,7,7],[5,6,6,10,10,7,7],[5,6,6,10,10,10,7],[5,6,7,7,7,7,7],[5,6,10,7,7,7,7],[5,6,10,10,7,7,7],[5,6,10,10,10,7,7],[5,6,10,10,10,10,7],[5,7,7,7,7,7,7],[5,9,3,3,3,7,7],[5,9,3,3,6,7,7],[5,9,3,3,7,7,7],[5,9,3,3,10,7,7],[5,9,3,6,6,7,7],[5,9,3,6,7,7,7],[5,9,3,6,10,7,7],[5,9,3,7,7,7,7],[5,9,3,10,7,7,7],[5,9,3,10,10,7,7],[5,9,6,6,6,7,7],[5,9,6,6,7,7,7],[5,9,6,6,10,7,7],[5,9,6,7,7,7,7],[5,9,6,10,7,7,7],[5,9,6,10,10,7,7],[5,9,7,7,7,7,7],[5,9,9,3,7,7,7],[5,9,9,6,7,7,7],[5,9,9,7,7,7,7],[5,9,9,10,7,7,7],[5,9,10,7,7,7,7],[5,9,10,10,7,7,7],[5,9,10,10,10,7,7],[5,10,7,7,7,7,7],[5,10,10,7,7,7,7],[5,10,10,10,7,7,7],[5,10,10,10,10,7,7],[5,10,10,10,10,10,7]] := by
  simp only [prefix7_5_3_3,prefix7_5_3_6,prefix7_5_3_7,prefix7_5_3_10,prefix7_5_5_3,prefix7_5_5_5,prefix7_5_5_6,prefix7_5_5_7,prefix7_5_5_9,prefix7_5_5_10,prefix7_5_6_6,prefix7_5_6_7,prefix7_5_6_10,prefix7_5_7_7,prefix7_5_9_3,prefix7_5_9_6,prefix7_5_9_7,prefix7_5_9_9,prefix7_5_9_10,prefix7_5_10_7,prefix7_5_10_10] <;> rfl
end ThreeBoundEndpoint22Types


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Sensitivity213981Formal
section
/- Exact bounded Type7 group. Generated source; requires Lean checking. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Types
open ThreeBoundQ3 ThreeBoundEndpoint22TypeSplit











































theorem _root_.solution :
    ((filteredPrefix ([5,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([5,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([5,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([5,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([5,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([5,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([5,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([5,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([5,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([5,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[5,3,3,3,3,3,7],[5,3,3,3,3,6,7],[5,3,3,3,3,7,7],[5,3,3,3,3,10,7],[5,3,3,3,6,6,7],[5,3,3,3,6,7,7],[5,3,3,3,6,10,7],[5,3,3,3,7,7,7],[5,3,3,3,10,7,7],[5,3,3,3,10,10,7],[5,3,3,6,6,6,7],[5,3,3,6,6,7,7],[5,3,3,6,6,10,7],[5,3,3,6,7,7,7],[5,3,3,6,10,7,7],[5,3,3,6,10,10,7],[5,3,3,7,7,7,7],[5,3,3,10,7,7,7],[5,3,3,10,10,7,7],[5,3,3,10,10,10,7],[5,3,6,6,6,6,7],[5,3,6,6,6,7,7],[5,3,6,6,6,10,7],[5,3,6,6,7,7,7],[5,3,6,6,10,7,7],[5,3,6,6,10,10,7],[5,3,6,7,7,7,7],[5,3,6,10,7,7,7],[5,3,6,10,10,7,7],[5,3,6,10,10,10,7],[5,3,7,7,7,7,7],[5,3,10,7,7,7,7],[5,3,10,10,7,7,7],[5,3,10,10,10,7,7],[5,3,10,10,10,10,7],[5,5,3,3,3,7,7],[5,5,3,3,6,7,7],[5,5,3,3,7,7,7],[5,5,3,3,10,7,7],[5,5,3,6,6,7,7],[5,5,3,6,7,7,7],[5,5,3,6,10,7,7],[5,5,3,7,7,7,7],[5,5,3,10,7,7,7],[5,5,3,10,10,7,7],[5,5,5,3,7,7,7],[5,5,5,6,7,7,7],[5,5,5,7,7,7,7],[5,5,5,10,7,7,7],[5,5,6,6,6,7,7],[5,5,6,6,7,7,7],[5,5,6,6,10,7,7],[5,5,6,7,7,7,7],[5,5,6,10,7,7,7],[5,5,6,10,10,7,7],[5,5,7,7,7,7,7],[5,5,9,3,7,7,7],[5,5,9,6,7,7,7],[5,5,9,7,7,7,7],[5,5,9,10,7,7,7],[5,5,10,7,7,7,7],[5,5,10,10,7,7,7],[5,5,10,10,10,7,7],[5,6,6,6,6,6,7],[5,6,6,6,6,7,7],[5,6,6,6,6,10,7],[5,6,6,6,7,7,7],[5,6,6,6,10,7,7],[5,6,6,6,10,10,7],[5,6,6,7,7,7,7],[5,6,6,10,7,7,7],[5,6,6,10,10,7,7],[5,6,6,10,10,10,7],[5,6,7,7,7,7,7],[5,6,10,7,7,7,7],[5,6,10,10,7,7,7],[5,6,10,10,10,7,7],[5,6,10,10,10,10,7],[5,7,7,7,7,7,7],[5,9,3,3,3,7,7],[5,9,3,3,6,7,7],[5,9,3,3,7,7,7],[5,9,3,3,10,7,7],[5,9,3,6,6,7,7],[5,9,3,6,7,7,7],[5,9,3,6,10,7,7],[5,9,3,7,7,7,7],[5,9,3,10,7,7,7],[5,9,3,10,10,7,7],[5,9,6,6,6,7,7],[5,9,6,6,7,7,7],[5,9,6,6,10,7,7],[5,9,6,7,7,7,7],[5,9,6,10,7,7,7],[5,9,6,10,10,7,7],[5,9,7,7,7,7,7],[5,9,9,3,7,7,7],[5,9,9,6,7,7,7],[5,9,9,7,7,7,7],[5,9,9,10,7,7,7],[5,9,10,7,7,7,7],[5,9,10,10,7,7,7],[5,9,10,10,10,7,7],[5,10,7,7,7,7,7],[5,10,10,7,7,7,7],[5,10,10,10,7,7,7],[5,10,10,10,10,7,7],[5,10,10,10,10,10,7]] := @Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group5_eq
end ThreeBoundEndpoint22Types


end
end Sensitivity213981Formal
