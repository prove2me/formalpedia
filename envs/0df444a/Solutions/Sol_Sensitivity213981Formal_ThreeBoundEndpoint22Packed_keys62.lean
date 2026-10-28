-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys62
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:20.757172+00:00
-- url     : https://prove2.me/submissions/d26bda48-659d-4e75-b237-d232aa6f7f5a

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree062
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData062
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
theorem keys62_0 : subtree62_0.checkKeys=true := by decide +kernel
theorem keys62_1 : subtree62_1.checkKeys=true := by decide +kernel
theorem keys62_2 : subtree62_2.checkKeys=true := by decide +kernel
theorem keys62_3 : subtree62_3.checkKeys=true := by decide +kernel
theorem keys62_4 : subtree62_4.checkKeys=true := by decide +kernel
theorem keys62_5 : subtree62_5.checkKeys=true := by decide +kernel
theorem keys62_6 : subtree62_6.checkKeys=true := by decide +kernel
theorem keys62_7 : subtree62_7.checkKeys=true := by decide +kernel
theorem keys62 : subtree62.checkKeys=true := by
  simp only [subtree62,Tree.checkKeys,keys62_0,keys62_1,keys62_2,keys62_3,keys62_4,keys62_5,keys62_6,keys62_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree62)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys62
