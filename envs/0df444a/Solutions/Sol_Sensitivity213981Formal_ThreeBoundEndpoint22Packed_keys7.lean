-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys7
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:35:48.26269+00:00
-- url     : https://prove2.me/submissions/efc30c0c-a571-4298-860e-84824c6d657b

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree007
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData007
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
theorem keys7_0 : subtree7_0.checkKeys=true := by decide +kernel
theorem keys7_1 : subtree7_1.checkKeys=true := by decide +kernel
theorem keys7_2 : subtree7_2.checkKeys=true := by decide +kernel
theorem keys7_3 : subtree7_3.checkKeys=true := by decide +kernel
theorem keys7_4 : subtree7_4.checkKeys=true := by decide +kernel
theorem keys7_5 : subtree7_5.checkKeys=true := by decide +kernel
theorem keys7_6 : subtree7_6.checkKeys=true := by decide +kernel
theorem keys7_7 : subtree7_7.checkKeys=true := by decide +kernel
theorem keys7 : subtree7.checkKeys=true := by
  simp only [subtree7,Tree.checkKeys,keys7_0,keys7_1,keys7_2,keys7_3,keys7_4,keys7_5,keys7_6,keys7_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree7)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys7
