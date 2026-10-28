-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group2_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:47:13.855258+00:00
-- url     : https://prove2.me/submissions/472d7f17-98bc-49ad-9965-38feb7dc14f5

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

private theorem prefix7_2_2_2 : filteredPrefix ([2,2,2] : List Kind) (orderKey (2 : Kind)) 4 = [[2,2,2,3,7,7,7],[2,2,2,6,7,7,7],[2,2,2,7,7,7,7],[2,2,2,10,7,7,7]] := by decide +kernel

private theorem prefix7_2_2_3 : filteredPrefix ([2,2,3] : List Kind) (orderKey (3 : Kind)) 4 = [[2,2,3,3,3,7,7],[2,2,3,3,6,7,7],[2,2,3,3,7,7,7],[2,2,3,3,10,7,7],[2,2,3,6,6,7,7],[2,2,3,6,7,7,7],[2,2,3,6,10,7,7],[2,2,3,7,7,7,7],[2,2,3,10,7,7,7],[2,2,3,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_2_5 : filteredPrefix ([2,2,5] : List Kind) (orderKey (5 : Kind)) 4 = [[2,2,5,3,7,7,7],[2,2,5,6,7,7,7],[2,2,5,7,7,7,7],[2,2,5,10,7,7,7]] := by decide +kernel

private theorem prefix7_2_2_6 : filteredPrefix ([2,2,6] : List Kind) (orderKey (6 : Kind)) 4 = [[2,2,6,6,6,7,7],[2,2,6,6,7,7,7],[2,2,6,6,10,7,7],[2,2,6,7,7,7,7],[2,2,6,10,7,7,7],[2,2,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_2_7 : filteredPrefix ([2,2,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,2,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_2_9 : filteredPrefix ([2,2,9] : List Kind) (orderKey (9 : Kind)) 4 = [[2,2,9,3,7,7,7],[2,2,9,6,7,7,7],[2,2,9,7,7,7,7],[2,2,9,10,7,7,7]] := by decide +kernel

private theorem prefix7_2_2_10 : filteredPrefix ([2,2,10] : List Kind) (orderKey (10 : Kind)) 4 = [[2,2,10,7,7,7,7],[2,2,10,10,7,7,7],[2,2,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_3_3 : filteredPrefix ([2,3,3] : List Kind) (orderKey (3 : Kind)) 4 = [[2,3,3,3,3,3,7],[2,3,3,3,3,6,7],[2,3,3,3,3,7,7],[2,3,3,3,3,10,7],[2,3,3,3,6,6,7],[2,3,3,3,6,7,7],[2,3,3,3,6,10,7],[2,3,3,3,7,7,7],[2,3,3,3,10,7,7],[2,3,3,3,10,10,7],[2,3,3,6,6,6,7],[2,3,3,6,6,7,7],[2,3,3,6,6,10,7],[2,3,3,6,7,7,7],[2,3,3,6,10,7,7],[2,3,3,6,10,10,7],[2,3,3,7,7,7,7],[2,3,3,10,7,7,7],[2,3,3,10,10,7,7],[2,3,3,10,10,10,7]] := by decide +kernel

private theorem prefix7_2_3_6 : filteredPrefix ([2,3,6] : List Kind) (orderKey (6 : Kind)) 4 = [[2,3,6,6,6,6,7],[2,3,6,6,6,7,7],[2,3,6,6,6,10,7],[2,3,6,6,7,7,7],[2,3,6,6,10,7,7],[2,3,6,6,10,10,7],[2,3,6,7,7,7,7],[2,3,6,10,7,7,7],[2,3,6,10,10,7,7],[2,3,6,10,10,10,7]] := by decide +kernel

private theorem prefix7_2_3_7 : filteredPrefix ([2,3,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,3,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_3_10 : filteredPrefix ([2,3,10] : List Kind) (orderKey (10 : Kind)) 4 = [[2,3,10,7,7,7,7],[2,3,10,10,7,7,7],[2,3,10,10,10,7,7],[2,3,10,10,10,10,7]] := by decide +kernel

private theorem prefix7_2_5_3 : filteredPrefix ([2,5,3] : List Kind) (orderKey (3 : Kind)) 4 = [[2,5,3,3,3,7,7],[2,5,3,3,6,7,7],[2,5,3,3,7,7,7],[2,5,3,3,10,7,7],[2,5,3,6,6,7,7],[2,5,3,6,7,7,7],[2,5,3,6,10,7,7],[2,5,3,7,7,7,7],[2,5,3,10,7,7,7],[2,5,3,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_5_5 : filteredPrefix ([2,5,5] : List Kind) (orderKey (5 : Kind)) 4 = [[2,5,5,3,7,7,7],[2,5,5,6,7,7,7],[2,5,5,7,7,7,7],[2,5,5,10,7,7,7]] := by decide +kernel

private theorem prefix7_2_5_6 : filteredPrefix ([2,5,6] : List Kind) (orderKey (6 : Kind)) 4 = [[2,5,6,6,6,7,7],[2,5,6,6,7,7,7],[2,5,6,6,10,7,7],[2,5,6,7,7,7,7],[2,5,6,10,7,7,7],[2,5,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_5_7 : filteredPrefix ([2,5,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,5,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_5_9 : filteredPrefix ([2,5,9] : List Kind) (orderKey (9 : Kind)) 4 = [[2,5,9,3,7,7,7],[2,5,9,6,7,7,7],[2,5,9,7,7,7,7],[2,5,9,10,7,7,7]] := by decide +kernel

private theorem prefix7_2_5_10 : filteredPrefix ([2,5,10] : List Kind) (orderKey (10 : Kind)) 4 = [[2,5,10,7,7,7,7],[2,5,10,10,7,7,7],[2,5,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_6_6 : filteredPrefix ([2,6,6] : List Kind) (orderKey (6 : Kind)) 4 = [[2,6,6,6,6,6,7],[2,6,6,6,6,7,7],[2,6,6,6,6,10,7],[2,6,6,6,7,7,7],[2,6,6,6,10,7,7],[2,6,6,6,10,10,7],[2,6,6,7,7,7,7],[2,6,6,10,7,7,7],[2,6,6,10,10,7,7],[2,6,6,10,10,10,7]] := by decide +kernel

private theorem prefix7_2_6_7 : filteredPrefix ([2,6,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,6,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_6_10 : filteredPrefix ([2,6,10] : List Kind) (orderKey (10 : Kind)) 4 = [[2,6,10,7,7,7,7],[2,6,10,10,7,7,7],[2,6,10,10,10,7,7],[2,6,10,10,10,10,7]] := by decide +kernel

private theorem prefix7_2_7_7 : filteredPrefix ([2,7,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,7,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_9_3 : filteredPrefix ([2,9,3] : List Kind) (orderKey (3 : Kind)) 4 = [[2,9,3,3,3,7,7],[2,9,3,3,6,7,7],[2,9,3,3,7,7,7],[2,9,3,3,10,7,7],[2,9,3,6,6,7,7],[2,9,3,6,7,7,7],[2,9,3,6,10,7,7],[2,9,3,7,7,7,7],[2,9,3,10,7,7,7],[2,9,3,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_9_6 : filteredPrefix ([2,9,6] : List Kind) (orderKey (6 : Kind)) 4 = [[2,9,6,6,6,7,7],[2,9,6,6,7,7,7],[2,9,6,6,10,7,7],[2,9,6,7,7,7,7],[2,9,6,10,7,7,7],[2,9,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_9_7 : filteredPrefix ([2,9,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,9,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_9_9 : filteredPrefix ([2,9,9] : List Kind) (orderKey (9 : Kind)) 4 = [[2,9,9,3,7,7,7],[2,9,9,6,7,7,7],[2,9,9,7,7,7,7],[2,9,9,10,7,7,7]] := by decide +kernel

private theorem prefix7_2_9_10 : filteredPrefix ([2,9,10] : List Kind) (orderKey (10 : Kind)) 4 = [[2,9,10,7,7,7,7],[2,9,10,10,7,7,7],[2,9,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_2_10_7 : filteredPrefix ([2,10,7] : List Kind) (orderKey (7 : Kind)) 4 = [[2,10,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_2_10_10 : filteredPrefix ([2,10,10] : List Kind) (orderKey (10 : Kind)) 4 = [[2,10,10,7,7,7,7],[2,10,10,10,7,7,7],[2,10,10,10,10,7,7],[2,10,10,10,10,10,7]] := by decide +kernel

theorem types7_group2_eq :
    ((filteredPrefix ([2,2,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([2,2,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,2,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([2,2,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,2,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,2,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,2,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([2,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[2,2,2,3,7,7,7],[2,2,2,6,7,7,7],[2,2,2,7,7,7,7],[2,2,2,10,7,7,7],[2,2,3,3,3,7,7],[2,2,3,3,6,7,7],[2,2,3,3,7,7,7],[2,2,3,3,10,7,7],[2,2,3,6,6,7,7],[2,2,3,6,7,7,7],[2,2,3,6,10,7,7],[2,2,3,7,7,7,7],[2,2,3,10,7,7,7],[2,2,3,10,10,7,7],[2,2,5,3,7,7,7],[2,2,5,6,7,7,7],[2,2,5,7,7,7,7],[2,2,5,10,7,7,7],[2,2,6,6,6,7,7],[2,2,6,6,7,7,7],[2,2,6,6,10,7,7],[2,2,6,7,7,7,7],[2,2,6,10,7,7,7],[2,2,6,10,10,7,7],[2,2,7,7,7,7,7],[2,2,9,3,7,7,7],[2,2,9,6,7,7,7],[2,2,9,7,7,7,7],[2,2,9,10,7,7,7],[2,2,10,7,7,7,7],[2,2,10,10,7,7,7],[2,2,10,10,10,7,7],[2,3,3,3,3,3,7],[2,3,3,3,3,6,7],[2,3,3,3,3,7,7],[2,3,3,3,3,10,7],[2,3,3,3,6,6,7],[2,3,3,3,6,7,7],[2,3,3,3,6,10,7],[2,3,3,3,7,7,7],[2,3,3,3,10,7,7],[2,3,3,3,10,10,7],[2,3,3,6,6,6,7],[2,3,3,6,6,7,7],[2,3,3,6,6,10,7],[2,3,3,6,7,7,7],[2,3,3,6,10,7,7],[2,3,3,6,10,10,7],[2,3,3,7,7,7,7],[2,3,3,10,7,7,7],[2,3,3,10,10,7,7],[2,3,3,10,10,10,7],[2,3,6,6,6,6,7],[2,3,6,6,6,7,7],[2,3,6,6,6,10,7],[2,3,6,6,7,7,7],[2,3,6,6,10,7,7],[2,3,6,6,10,10,7],[2,3,6,7,7,7,7],[2,3,6,10,7,7,7],[2,3,6,10,10,7,7],[2,3,6,10,10,10,7],[2,3,7,7,7,7,7],[2,3,10,7,7,7,7],[2,3,10,10,7,7,7],[2,3,10,10,10,7,7],[2,3,10,10,10,10,7],[2,5,3,3,3,7,7],[2,5,3,3,6,7,7],[2,5,3,3,7,7,7],[2,5,3,3,10,7,7],[2,5,3,6,6,7,7],[2,5,3,6,7,7,7],[2,5,3,6,10,7,7],[2,5,3,7,7,7,7],[2,5,3,10,7,7,7],[2,5,3,10,10,7,7],[2,5,5,3,7,7,7],[2,5,5,6,7,7,7],[2,5,5,7,7,7,7],[2,5,5,10,7,7,7],[2,5,6,6,6,7,7],[2,5,6,6,7,7,7],[2,5,6,6,10,7,7],[2,5,6,7,7,7,7],[2,5,6,10,7,7,7],[2,5,6,10,10,7,7],[2,5,7,7,7,7,7],[2,5,9,3,7,7,7],[2,5,9,6,7,7,7],[2,5,9,7,7,7,7],[2,5,9,10,7,7,7],[2,5,10,7,7,7,7],[2,5,10,10,7,7,7],[2,5,10,10,10,7,7],[2,6,6,6,6,6,7],[2,6,6,6,6,7,7],[2,6,6,6,6,10,7],[2,6,6,6,7,7,7],[2,6,6,6,10,7,7],[2,6,6,6,10,10,7],[2,6,6,7,7,7,7],[2,6,6,10,7,7,7],[2,6,6,10,10,7,7],[2,6,6,10,10,10,7],[2,6,7,7,7,7,7],[2,6,10,7,7,7,7],[2,6,10,10,7,7,7],[2,6,10,10,10,7,7],[2,6,10,10,10,10,7],[2,7,7,7,7,7,7],[2,9,3,3,3,7,7],[2,9,3,3,6,7,7],[2,9,3,3,7,7,7],[2,9,3,3,10,7,7],[2,9,3,6,6,7,7],[2,9,3,6,7,7,7],[2,9,3,6,10,7,7],[2,9,3,7,7,7,7],[2,9,3,10,7,7,7],[2,9,3,10,10,7,7],[2,9,6,6,6,7,7],[2,9,6,6,7,7,7],[2,9,6,6,10,7,7],[2,9,6,7,7,7,7],[2,9,6,10,7,7,7],[2,9,6,10,10,7,7],[2,9,7,7,7,7,7],[2,9,9,3,7,7,7],[2,9,9,6,7,7,7],[2,9,9,7,7,7,7],[2,9,9,10,7,7,7],[2,9,10,7,7,7,7],[2,9,10,10,7,7,7],[2,9,10,10,10,7,7],[2,10,7,7,7,7,7],[2,10,10,7,7,7,7],[2,10,10,10,7,7,7],[2,10,10,10,10,7,7],[2,10,10,10,10,10,7]] := by
  simp only [prefix7_2_2_2,prefix7_2_2_3,prefix7_2_2_5,prefix7_2_2_6,prefix7_2_2_7,prefix7_2_2_9,prefix7_2_2_10,prefix7_2_3_3,prefix7_2_3_6,prefix7_2_3_7,prefix7_2_3_10,prefix7_2_5_3,prefix7_2_5_5,prefix7_2_5_6,prefix7_2_5_7,prefix7_2_5_9,prefix7_2_5_10,prefix7_2_6_6,prefix7_2_6_7,prefix7_2_6_10,prefix7_2_7_7,prefix7_2_9_3,prefix7_2_9_6,prefix7_2_9_7,prefix7_2_9_9,prefix7_2_9_10,prefix7_2_10_7,prefix7_2_10_10] <;> rfl
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
    ((filteredPrefix ([2,2,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([2,2,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,2,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([2,2,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,2,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,2,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,2,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([2,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([2,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([2,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([2,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([2,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([2,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[2,2,2,3,7,7,7],[2,2,2,6,7,7,7],[2,2,2,7,7,7,7],[2,2,2,10,7,7,7],[2,2,3,3,3,7,7],[2,2,3,3,6,7,7],[2,2,3,3,7,7,7],[2,2,3,3,10,7,7],[2,2,3,6,6,7,7],[2,2,3,6,7,7,7],[2,2,3,6,10,7,7],[2,2,3,7,7,7,7],[2,2,3,10,7,7,7],[2,2,3,10,10,7,7],[2,2,5,3,7,7,7],[2,2,5,6,7,7,7],[2,2,5,7,7,7,7],[2,2,5,10,7,7,7],[2,2,6,6,6,7,7],[2,2,6,6,7,7,7],[2,2,6,6,10,7,7],[2,2,6,7,7,7,7],[2,2,6,10,7,7,7],[2,2,6,10,10,7,7],[2,2,7,7,7,7,7],[2,2,9,3,7,7,7],[2,2,9,6,7,7,7],[2,2,9,7,7,7,7],[2,2,9,10,7,7,7],[2,2,10,7,7,7,7],[2,2,10,10,7,7,7],[2,2,10,10,10,7,7],[2,3,3,3,3,3,7],[2,3,3,3,3,6,7],[2,3,3,3,3,7,7],[2,3,3,3,3,10,7],[2,3,3,3,6,6,7],[2,3,3,3,6,7,7],[2,3,3,3,6,10,7],[2,3,3,3,7,7,7],[2,3,3,3,10,7,7],[2,3,3,3,10,10,7],[2,3,3,6,6,6,7],[2,3,3,6,6,7,7],[2,3,3,6,6,10,7],[2,3,3,6,7,7,7],[2,3,3,6,10,7,7],[2,3,3,6,10,10,7],[2,3,3,7,7,7,7],[2,3,3,10,7,7,7],[2,3,3,10,10,7,7],[2,3,3,10,10,10,7],[2,3,6,6,6,6,7],[2,3,6,6,6,7,7],[2,3,6,6,6,10,7],[2,3,6,6,7,7,7],[2,3,6,6,10,7,7],[2,3,6,6,10,10,7],[2,3,6,7,7,7,7],[2,3,6,10,7,7,7],[2,3,6,10,10,7,7],[2,3,6,10,10,10,7],[2,3,7,7,7,7,7],[2,3,10,7,7,7,7],[2,3,10,10,7,7,7],[2,3,10,10,10,7,7],[2,3,10,10,10,10,7],[2,5,3,3,3,7,7],[2,5,3,3,6,7,7],[2,5,3,3,7,7,7],[2,5,3,3,10,7,7],[2,5,3,6,6,7,7],[2,5,3,6,7,7,7],[2,5,3,6,10,7,7],[2,5,3,7,7,7,7],[2,5,3,10,7,7,7],[2,5,3,10,10,7,7],[2,5,5,3,7,7,7],[2,5,5,6,7,7,7],[2,5,5,7,7,7,7],[2,5,5,10,7,7,7],[2,5,6,6,6,7,7],[2,5,6,6,7,7,7],[2,5,6,6,10,7,7],[2,5,6,7,7,7,7],[2,5,6,10,7,7,7],[2,5,6,10,10,7,7],[2,5,7,7,7,7,7],[2,5,9,3,7,7,7],[2,5,9,6,7,7,7],[2,5,9,7,7,7,7],[2,5,9,10,7,7,7],[2,5,10,7,7,7,7],[2,5,10,10,7,7,7],[2,5,10,10,10,7,7],[2,6,6,6,6,6,7],[2,6,6,6,6,7,7],[2,6,6,6,6,10,7],[2,6,6,6,7,7,7],[2,6,6,6,10,7,7],[2,6,6,6,10,10,7],[2,6,6,7,7,7,7],[2,6,6,10,7,7,7],[2,6,6,10,10,7,7],[2,6,6,10,10,10,7],[2,6,7,7,7,7,7],[2,6,10,7,7,7,7],[2,6,10,10,7,7,7],[2,6,10,10,10,7,7],[2,6,10,10,10,10,7],[2,7,7,7,7,7,7],[2,9,3,3,3,7,7],[2,9,3,3,6,7,7],[2,9,3,3,7,7,7],[2,9,3,3,10,7,7],[2,9,3,6,6,7,7],[2,9,3,6,7,7,7],[2,9,3,6,10,7,7],[2,9,3,7,7,7,7],[2,9,3,10,7,7,7],[2,9,3,10,10,7,7],[2,9,6,6,6,7,7],[2,9,6,6,7,7,7],[2,9,6,6,10,7,7],[2,9,6,7,7,7,7],[2,9,6,10,7,7,7],[2,9,6,10,10,7,7],[2,9,7,7,7,7,7],[2,9,9,3,7,7,7],[2,9,9,6,7,7,7],[2,9,9,7,7,7,7],[2,9,9,10,7,7,7],[2,9,10,7,7,7,7],[2,9,10,10,7,7,7],[2,9,10,10,10,7,7],[2,10,7,7,7,7,7],[2,10,10,7,7,7,7],[2,10,10,10,7,7,7],[2,10,10,10,10,7,7],[2,10,10,10,10,10,7]] := @Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group2_eq
end ThreeBoundEndpoint22Types


end
end Sensitivity213981Formal
