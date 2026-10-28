-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys41
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:40:44.067529+00:00
-- url     : https://prove2.me/submissions/cf86cfd0-7ff1-4533-892c-54f2e80c6166

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


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRelaxedPacked
theorem keys41_0 : subtree41_0.checkKeys=true := by decide +kernel
theorem keys41_1 : subtree41_1.checkKeys=true := by decide +kernel
theorem keys41_2 : subtree41_2.checkKeys=true := by decide +kernel
theorem keys41_3 : subtree41_3.checkKeys=true := by decide +kernel
theorem keys41_4 : subtree41_4.checkKeys=true := by decide +kernel
theorem keys41_5 : subtree41_5.checkKeys=true := by decide +kernel
theorem keys41_6 : subtree41_6.checkKeys=true := by decide +kernel
theorem keys41_7 : subtree41_7.checkKeys=true := by decide +kernel
theorem keys41 : subtree41.checkKeys=true := by
  simp only [subtree41,Tree.checkKeys,keys41_0,keys41_1,keys41_2,keys41_3,keys41_4,keys41_5,keys41_6,keys41_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree41)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys41
