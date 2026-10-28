-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys70
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:06.199498+00:00
-- url     : https://prove2.me/submissions/f6978d19-6c74-4469-b890-bbe397f66801

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree070
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData070
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
theorem keys70_0 : subtree70_0.checkKeys=true := by decide +kernel
theorem keys70_1 : subtree70_1.checkKeys=true := by decide +kernel
theorem keys70_2 : subtree70_2.checkKeys=true := by decide +kernel
theorem keys70_3 : subtree70_3.checkKeys=true := by decide +kernel
theorem keys70_4 : subtree70_4.checkKeys=true := by decide +kernel
theorem keys70_5 : subtree70_5.checkKeys=true := by decide +kernel
theorem keys70_6 : subtree70_6.checkKeys=true := by decide +kernel
theorem keys70_7 : subtree70_7.checkKeys=true := by decide +kernel
theorem keys70 : subtree70.checkKeys=true := by
  simp only [subtree70,Tree.checkKeys,keys70_0,keys70_1,keys70_2,keys70_3,keys70_4,keys70_5,keys70_6,keys70_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree70)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys70
