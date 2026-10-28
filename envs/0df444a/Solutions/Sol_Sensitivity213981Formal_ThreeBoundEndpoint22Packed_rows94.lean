-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows94
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:02:39.067983+00:00
-- url     : https://prove2.me/submissions/5d4c7236-03e1-470e-b4e3-15fa624b30aa

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree094
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData094
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeMatch
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedPacked_Tree_matches_rows


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRelaxedPacked









theorem shape94 : subtree94.Matches ThreeBoundEndpoint22Records.subtree94 := by
  simp only [subtree94,subtree94_0,subtree94_1,subtree94_2,subtree94_3,subtree94_4,subtree94_5,subtree94_6,subtree94_7,ThreeBoundEndpoint22Records.subtree94,Tree.Matches,eq_self_iff_true,and_self]
theorem rows94 : subtree94.rows=ThreeBoundEndpoint22Records.subtree94.elements := Tree.matches_rows _ _ shape94
end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} (List.{0} (List.{0} Nat))
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree94)
  (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.subtree94) := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows94
