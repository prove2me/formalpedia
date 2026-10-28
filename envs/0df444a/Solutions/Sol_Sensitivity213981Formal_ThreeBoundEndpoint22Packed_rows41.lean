-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows41
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:58:05.234599+00:00
-- url     : https://prove2.me/submissions/a0afdaaa-49e8-4ea3-9f1a-7a9ed7c963c8

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree041
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData041
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









theorem shape41 : subtree41.Matches ThreeBoundEndpoint22Records.subtree41 := by
  simp only [subtree41,subtree41_0,subtree41_1,subtree41_2,subtree41_3,subtree41_4,subtree41_5,subtree41_6,subtree41_7,ThreeBoundEndpoint22Records.subtree41,Tree.Matches,eq_self_iff_true,and_self]
theorem rows41 : subtree41.rows=ThreeBoundEndpoint22Records.subtree41.elements := Tree.matches_rows _ _ shape41
end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} (List.{0} (List.{0} Nat))
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree41)
  (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.subtree41) := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.rows41
