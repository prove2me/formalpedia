-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group1_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:05:44.145487+00:00
-- url     : https://prove2.me/submissions/d0faf668-0063-4387-a356-e8a5ca818331

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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22TypeSplit_filteredPrefix_eq_nil_of_budget


namespace Sensitivity213981Formal
section
/- Exact bounded Type7 group. Generated source; requires Lean checking. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Types
open ThreeBoundQ3 ThreeBoundEndpoint22TypeSplit

private theorem prefix7_1_1_1 : filteredPrefix ([1,1,1] : List Kind) (orderKey (1 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,1] : List Kind) (orderKey (1 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_1_2 : filteredPrefix ([1,1,2] : List Kind) (orderKey (2 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,2] : List Kind) (orderKey (2 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_1_3 : filteredPrefix ([1,1,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,1,3,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_1_4 : filteredPrefix ([1,1,4] : List Kind) (orderKey (4 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,4] : List Kind) (orderKey (4 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_1_5 : filteredPrefix ([1,1,5] : List Kind) (orderKey (5 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,5] : List Kind) (orderKey (5 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_1_6 : filteredPrefix ([1,1,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,1,6,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_1_7 : filteredPrefix ([1,1,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,1,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_1_8 : filteredPrefix ([1,1,8] : List Kind) (orderKey (8 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,8] : List Kind) (orderKey (8 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_1_9 : filteredPrefix ([1,1,9] : List Kind) (orderKey (9 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,1,9] : List Kind) (orderKey (9 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_1_10 : filteredPrefix ([1,1,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,1,10,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_2 : filteredPrefix ([1,2,2] : List Kind) (orderKey (2 : Kind)) 4 = [[1,2,2,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_3 : filteredPrefix ([1,2,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,2,3,3,7,7,7],[1,2,3,6,7,7,7],[1,2,3,7,7,7,7],[1,2,3,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_5 : filteredPrefix ([1,2,5] : List Kind) (orderKey (5 : Kind)) 4 = [[1,2,5,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_6 : filteredPrefix ([1,2,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,2,6,6,7,7,7],[1,2,6,7,7,7,7],[1,2,6,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_7 : filteredPrefix ([1,2,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,2,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_9 : filteredPrefix ([1,2,9] : List Kind) (orderKey (9 : Kind)) 4 = [[1,2,9,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_2_10 : filteredPrefix ([1,2,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,2,10,7,7,7,7],[1,2,10,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_3_3 : filteredPrefix ([1,3,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,3,3,3,3,7,7],[1,3,3,3,6,7,7],[1,3,3,3,7,7,7],[1,3,3,3,10,7,7],[1,3,3,6,6,7,7],[1,3,3,6,7,7,7],[1,3,3,6,10,7,7],[1,3,3,7,7,7,7],[1,3,3,10,7,7,7],[1,3,3,10,10,7,7]] := by decide +kernel

private theorem prefix7_1_3_6 : filteredPrefix ([1,3,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,3,6,6,6,7,7],[1,3,6,6,7,7,7],[1,3,6,6,10,7,7],[1,3,6,7,7,7,7],[1,3,6,10,7,7,7],[1,3,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_1_3_7 : filteredPrefix ([1,3,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,3,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_3_10 : filteredPrefix ([1,3,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,3,10,7,7,7,7],[1,3,10,10,7,7,7],[1,3,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_1_4_2 : filteredPrefix ([1,4,2] : List Kind) (orderKey (2 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,2] : List Kind) (orderKey (2 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_4_3 : filteredPrefix ([1,4,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,4,3,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_4_4 : filteredPrefix ([1,4,4] : List Kind) (orderKey (4 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,4] : List Kind) (orderKey (4 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_4_5 : filteredPrefix ([1,4,5] : List Kind) (orderKey (5 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,5] : List Kind) (orderKey (5 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_4_6 : filteredPrefix ([1,4,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,4,6,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_4_7 : filteredPrefix ([1,4,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,4,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_4_8 : filteredPrefix ([1,4,8] : List Kind) (orderKey (8 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,8] : List Kind) (orderKey (8 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_4_9 : filteredPrefix ([1,4,9] : List Kind) (orderKey (9 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,4,9] : List Kind) (orderKey (9 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_4_10 : filteredPrefix ([1,4,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,4,10,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_5_3 : filteredPrefix ([1,5,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,5,3,3,7,7,7],[1,5,3,6,7,7,7],[1,5,3,7,7,7,7],[1,5,3,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_5_5 : filteredPrefix ([1,5,5] : List Kind) (orderKey (5 : Kind)) 4 = [[1,5,5,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_5_6 : filteredPrefix ([1,5,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,5,6,6,7,7,7],[1,5,6,7,7,7,7],[1,5,6,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_5_7 : filteredPrefix ([1,5,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,5,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_5_9 : filteredPrefix ([1,5,9] : List Kind) (orderKey (9 : Kind)) 4 = [[1,5,9,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_5_10 : filteredPrefix ([1,5,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,5,10,7,7,7,7],[1,5,10,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_6_6 : filteredPrefix ([1,6,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,6,6,6,6,7,7],[1,6,6,6,7,7,7],[1,6,6,6,10,7,7],[1,6,6,7,7,7,7],[1,6,6,10,7,7,7],[1,6,6,10,10,7,7]] := by decide +kernel

private theorem prefix7_1_6_7 : filteredPrefix ([1,6,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,6,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_6_10 : filteredPrefix ([1,6,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,6,10,7,7,7,7],[1,6,10,10,7,7,7],[1,6,10,10,10,7,7]] := by decide +kernel

private theorem prefix7_1_7_7 : filteredPrefix ([1,7,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,7,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_8_2 : filteredPrefix ([1,8,2] : List Kind) (orderKey (2 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,2] : List Kind) (orderKey (2 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_8_3 : filteredPrefix ([1,8,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,8,3,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_8_5 : filteredPrefix ([1,8,5] : List Kind) (orderKey (5 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,5] : List Kind) (orderKey (5 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_8_6 : filteredPrefix ([1,8,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,8,6,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_8_7 : filteredPrefix ([1,8,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,8,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_8_8 : filteredPrefix ([1,8,8] : List Kind) (orderKey (8 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,8] : List Kind) (orderKey (8 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_8_9 : filteredPrefix ([1,8,9] : List Kind) (orderKey (9 : Kind)) 4 = [] := by
  exact filteredPrefix_eq_nil_of_budget ([1,8,9] : List Kind) (orderKey (9 : Kind)) 4 (by decide +kernel)

private theorem prefix7_1_8_10 : filteredPrefix ([1,8,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,8,10,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_9_3 : filteredPrefix ([1,9,3] : List Kind) (orderKey (3 : Kind)) 4 = [[1,9,3,3,7,7,7],[1,9,3,6,7,7,7],[1,9,3,7,7,7,7],[1,9,3,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_9_6 : filteredPrefix ([1,9,6] : List Kind) (orderKey (6 : Kind)) 4 = [[1,9,6,6,7,7,7],[1,9,6,7,7,7,7],[1,9,6,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_9_7 : filteredPrefix ([1,9,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,9,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_9_9 : filteredPrefix ([1,9,9] : List Kind) (orderKey (9 : Kind)) 4 = [[1,9,9,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_9_10 : filteredPrefix ([1,9,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,9,10,7,7,7,7],[1,9,10,10,7,7,7]] := by decide +kernel

private theorem prefix7_1_10_7 : filteredPrefix ([1,10,7] : List Kind) (orderKey (7 : Kind)) 4 = [[1,10,7,7,7,7,7]] := by decide +kernel

private theorem prefix7_1_10_10 : filteredPrefix ([1,10,10] : List Kind) (orderKey (10 : Kind)) 4 = [[1,10,10,7,7,7,7],[1,10,10,10,7,7,7],[1,10,10,10,10,7,7]] := by decide +kernel

theorem types7_group1_eq :
    ((filteredPrefix ([1,1,1] : List Kind) (orderKey (1 : Kind)) 4 ++ filteredPrefix ([1,1,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,1,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,1,4] : List Kind) (orderKey (4 : Kind)) 4 ++ filteredPrefix ([1,1,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,1,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,1,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,1,8] : List Kind) (orderKey (8 : Kind)) 4 ++ filteredPrefix ([1,1,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,1,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,2,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,2,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,2,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,2,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,2,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,2,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,2,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,4,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,4,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,4,4] : List Kind) (orderKey (4 : Kind)) 4 ++ filteredPrefix ([1,4,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,4,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,4,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,4,8] : List Kind) (orderKey (8 : Kind)) 4 ++ filteredPrefix ([1,4,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,4,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,8,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,8,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,8,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,8,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,8,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,8,8] : List Kind) (orderKey (8 : Kind)) 4 ++ filteredPrefix ([1,8,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,8,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[1,1,3,7,7,7,7],[1,1,6,7,7,7,7],[1,1,7,7,7,7,7],[1,1,10,7,7,7,7],[1,2,2,7,7,7,7],[1,2,3,3,7,7,7],[1,2,3,6,7,7,7],[1,2,3,7,7,7,7],[1,2,3,10,7,7,7],[1,2,5,7,7,7,7],[1,2,6,6,7,7,7],[1,2,6,7,7,7,7],[1,2,6,10,7,7,7],[1,2,7,7,7,7,7],[1,2,9,7,7,7,7],[1,2,10,7,7,7,7],[1,2,10,10,7,7,7],[1,3,3,3,3,7,7],[1,3,3,3,6,7,7],[1,3,3,3,7,7,7],[1,3,3,3,10,7,7],[1,3,3,6,6,7,7],[1,3,3,6,7,7,7],[1,3,3,6,10,7,7],[1,3,3,7,7,7,7],[1,3,3,10,7,7,7],[1,3,3,10,10,7,7],[1,3,6,6,6,7,7],[1,3,6,6,7,7,7],[1,3,6,6,10,7,7],[1,3,6,7,7,7,7],[1,3,6,10,7,7,7],[1,3,6,10,10,7,7],[1,3,7,7,7,7,7],[1,3,10,7,7,7,7],[1,3,10,10,7,7,7],[1,3,10,10,10,7,7],[1,4,3,7,7,7,7],[1,4,6,7,7,7,7],[1,4,7,7,7,7,7],[1,4,10,7,7,7,7],[1,5,3,3,7,7,7],[1,5,3,6,7,7,7],[1,5,3,7,7,7,7],[1,5,3,10,7,7,7],[1,5,5,7,7,7,7],[1,5,6,6,7,7,7],[1,5,6,7,7,7,7],[1,5,6,10,7,7,7],[1,5,7,7,7,7,7],[1,5,9,7,7,7,7],[1,5,10,7,7,7,7],[1,5,10,10,7,7,7],[1,6,6,6,6,7,7],[1,6,6,6,7,7,7],[1,6,6,6,10,7,7],[1,6,6,7,7,7,7],[1,6,6,10,7,7,7],[1,6,6,10,10,7,7],[1,6,7,7,7,7,7],[1,6,10,7,7,7,7],[1,6,10,10,7,7,7],[1,6,10,10,10,7,7],[1,7,7,7,7,7,7],[1,8,3,7,7,7,7],[1,8,6,7,7,7,7],[1,8,7,7,7,7,7],[1,8,10,7,7,7,7],[1,9,3,3,7,7,7],[1,9,3,6,7,7,7],[1,9,3,7,7,7,7],[1,9,3,10,7,7,7],[1,9,6,6,7,7,7],[1,9,6,7,7,7,7],[1,9,6,10,7,7,7],[1,9,7,7,7,7,7],[1,9,9,7,7,7,7],[1,9,10,7,7,7,7],[1,9,10,10,7,7,7],[1,10,7,7,7,7,7],[1,10,10,7,7,7,7],[1,10,10,10,7,7,7],[1,10,10,10,10,7,7]] := by
  simp only [prefix7_1_1_1,prefix7_1_1_2,prefix7_1_1_3,prefix7_1_1_4,prefix7_1_1_5,prefix7_1_1_6,prefix7_1_1_7,prefix7_1_1_8,prefix7_1_1_9,prefix7_1_1_10,prefix7_1_2_2,prefix7_1_2_3,prefix7_1_2_5,prefix7_1_2_6,prefix7_1_2_7,prefix7_1_2_9,prefix7_1_2_10,prefix7_1_3_3,prefix7_1_3_6,prefix7_1_3_7,prefix7_1_3_10,prefix7_1_4_2,prefix7_1_4_3,prefix7_1_4_4,prefix7_1_4_5,prefix7_1_4_6,prefix7_1_4_7,prefix7_1_4_8,prefix7_1_4_9,prefix7_1_4_10,prefix7_1_5_3,prefix7_1_5_5,prefix7_1_5_6,prefix7_1_5_7,prefix7_1_5_9,prefix7_1_5_10,prefix7_1_6_6,prefix7_1_6_7,prefix7_1_6_10,prefix7_1_7_7,prefix7_1_8_2,prefix7_1_8_3,prefix7_1_8_5,prefix7_1_8_6,prefix7_1_8_7,prefix7_1_8_8,prefix7_1_8_9,prefix7_1_8_10,prefix7_1_9_3,prefix7_1_9_6,prefix7_1_9_7,prefix7_1_9_9,prefix7_1_9_10,prefix7_1_10_7,prefix7_1_10_10] <;> rfl
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
    ((filteredPrefix ([1,1,1] : List Kind) (orderKey (1 : Kind)) 4 ++ filteredPrefix ([1,1,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,1,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,1,4] : List Kind) (orderKey (4 : Kind)) 4 ++ filteredPrefix ([1,1,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,1,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,1,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,1,8] : List Kind) (orderKey (8 : Kind)) 4 ++ filteredPrefix ([1,1,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,1,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,2,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,2,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,2,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,2,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,2,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,2,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,2,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,3,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,3,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,3,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,3,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,4,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,4,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,4,4] : List Kind) (orderKey (4 : Kind)) 4 ++ filteredPrefix ([1,4,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,4,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,4,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,4,8] : List Kind) (orderKey (8 : Kind)) 4 ++ filteredPrefix ([1,4,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,4,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,5,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,5,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,5,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,5,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,5,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,5,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,6,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,6,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,6,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,7,7] : List Kind) (orderKey (7 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,8,2] : List Kind) (orderKey (2 : Kind)) 4 ++ filteredPrefix ([1,8,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,8,5] : List Kind) (orderKey (5 : Kind)) 4 ++ filteredPrefix ([1,8,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,8,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,8,8] : List Kind) (orderKey (8 : Kind)) 4 ++ filteredPrefix ([1,8,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,8,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,9,3] : List Kind) (orderKey (3 : Kind)) 4 ++ filteredPrefix ([1,9,6] : List Kind) (orderKey (6 : Kind)) 4 ++ filteredPrefix ([1,9,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,9,9] : List Kind) (orderKey (9 : Kind)) 4 ++ filteredPrefix ([1,9,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ (filteredPrefix ([1,10,7] : List Kind) (orderKey (7 : Kind)) 4 ++ filteredPrefix ([1,10,10] : List Kind) (orderKey (10 : Kind)) 4 ++ []) ++ []) =
      [[1,1,3,7,7,7,7],[1,1,6,7,7,7,7],[1,1,7,7,7,7,7],[1,1,10,7,7,7,7],[1,2,2,7,7,7,7],[1,2,3,3,7,7,7],[1,2,3,6,7,7,7],[1,2,3,7,7,7,7],[1,2,3,10,7,7,7],[1,2,5,7,7,7,7],[1,2,6,6,7,7,7],[1,2,6,7,7,7,7],[1,2,6,10,7,7,7],[1,2,7,7,7,7,7],[1,2,9,7,7,7,7],[1,2,10,7,7,7,7],[1,2,10,10,7,7,7],[1,3,3,3,3,7,7],[1,3,3,3,6,7,7],[1,3,3,3,7,7,7],[1,3,3,3,10,7,7],[1,3,3,6,6,7,7],[1,3,3,6,7,7,7],[1,3,3,6,10,7,7],[1,3,3,7,7,7,7],[1,3,3,10,7,7,7],[1,3,3,10,10,7,7],[1,3,6,6,6,7,7],[1,3,6,6,7,7,7],[1,3,6,6,10,7,7],[1,3,6,7,7,7,7],[1,3,6,10,7,7,7],[1,3,6,10,10,7,7],[1,3,7,7,7,7,7],[1,3,10,7,7,7,7],[1,3,10,10,7,7,7],[1,3,10,10,10,7,7],[1,4,3,7,7,7,7],[1,4,6,7,7,7,7],[1,4,7,7,7,7,7],[1,4,10,7,7,7,7],[1,5,3,3,7,7,7],[1,5,3,6,7,7,7],[1,5,3,7,7,7,7],[1,5,3,10,7,7,7],[1,5,5,7,7,7,7],[1,5,6,6,7,7,7],[1,5,6,7,7,7,7],[1,5,6,10,7,7,7],[1,5,7,7,7,7,7],[1,5,9,7,7,7,7],[1,5,10,7,7,7,7],[1,5,10,10,7,7,7],[1,6,6,6,6,7,7],[1,6,6,6,7,7,7],[1,6,6,6,10,7,7],[1,6,6,7,7,7,7],[1,6,6,10,7,7,7],[1,6,6,10,10,7,7],[1,6,7,7,7,7,7],[1,6,10,7,7,7,7],[1,6,10,10,7,7,7],[1,6,10,10,10,7,7],[1,7,7,7,7,7,7],[1,8,3,7,7,7,7],[1,8,6,7,7,7,7],[1,8,7,7,7,7,7],[1,8,10,7,7,7,7],[1,9,3,3,7,7,7],[1,9,3,6,7,7,7],[1,9,3,7,7,7,7],[1,9,3,10,7,7,7],[1,9,6,6,7,7,7],[1,9,6,7,7,7,7],[1,9,6,10,7,7,7],[1,9,7,7,7,7,7],[1,9,9,7,7,7,7],[1,9,10,7,7,7,7],[1,9,10,10,7,7,7],[1,10,7,7,7,7,7],[1,10,10,7,7,7,7],[1,10,10,10,7,7,7],[1,10,10,10,10,7,7]] := @Sensitivity213981Formal.ThreeBoundEndpoint22Types.types7_group1_eq
end ThreeBoundEndpoint22Types


end
end Sensitivity213981Formal
