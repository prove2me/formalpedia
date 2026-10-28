-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys35
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:57.561314+00:00
-- url     : https://prove2.me/submissions/3c7fae81-dbdd-4940-b97c-c635c006e263

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree035
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData035
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


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRelaxedPacked
theorem keys35_0 : subtree35_0.checkKeys=true := by decide +kernel
theorem keys35_1 : subtree35_1.checkKeys=true := by decide +kernel
theorem keys35_2 : subtree35_2.checkKeys=true := by decide +kernel
theorem keys35_3 : subtree35_3.checkKeys=true := by decide +kernel
theorem keys35_4 : subtree35_4.checkKeys=true := by decide +kernel
theorem keys35_5 : subtree35_5.checkKeys=true := by decide +kernel
theorem keys35_6 : subtree35_6.checkKeys=true := by decide +kernel
theorem keys35_7 : subtree35_7.checkKeys=true := by decide +kernel
theorem keys35 : subtree35.checkKeys=true := by
  simp only [subtree35,Tree.checkKeys,keys35_0,keys35_1,keys35_2,keys35_3,keys35_4,keys35_5,keys35_6,keys35_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree35)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys35
