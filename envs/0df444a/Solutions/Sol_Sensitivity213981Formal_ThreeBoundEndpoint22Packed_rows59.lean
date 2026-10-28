-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows59
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:00:28.733251+00:00
-- url     : https://prove2.me/submissions/2f002f21-33da-418b-a5a1-9e7a9ab0d6f9

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree059
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData059
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









theorem shape59 : subtree59.Matches ThreeBoundEndpoint22Records.subtree59 := by
  simp only [subtree59,subtree59_0,subtree59_1,subtree59_2,subtree59_3,subtree59_4,subtree59_5,subtree59_6,subtree59_7,ThreeBoundEndpoint22Records.subtree59,Tree.Matches,eq_self_iff_true,and_self]
theorem rows59 : subtree59.rows=ThreeBoundEndpoint22Records.subtree59.elements := Tree.matches_rows _ _ shape59
end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} (List.{0} (List.{0} Nat))
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree59)
  (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.subtree59) := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows59
