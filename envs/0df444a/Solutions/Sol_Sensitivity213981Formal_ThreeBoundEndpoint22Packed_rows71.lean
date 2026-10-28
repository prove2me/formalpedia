-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows71
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:00:47.161514+00:00
-- url     : https://prove2.me/submissions/cce6fcea-533b-41da-9d0a-93c372166acf

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree071
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData071
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









theorem shape71 : subtree71.Matches ThreeBoundEndpoint22Records.subtree71 := by
  simp only [subtree71,subtree71_0,subtree71_1,subtree71_2,subtree71_3,subtree71_4,subtree71_5,subtree71_6,subtree71_7,ThreeBoundEndpoint22Records.subtree71,Tree.Matches,eq_self_iff_true,and_self]
theorem rows71 : subtree71.rows=ThreeBoundEndpoint22Records.subtree71.elements := Tree.matches_rows _ _ shape71
end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} (List.{0} (List.{0} Nat))
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree71)
  (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.subtree71) := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows71
