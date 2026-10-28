-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys45
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:41:03.455467+00:00
-- url     : https://prove2.me/submissions/4dd33b04-3aa7-4cbf-9958-afd257264f7c

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree045
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData045
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
theorem keys45_0 : subtree45_0.checkKeys=true := by decide +kernel
theorem keys45_1 : subtree45_1.checkKeys=true := by decide +kernel
theorem keys45_2 : subtree45_2.checkKeys=true := by decide +kernel
theorem keys45_3 : subtree45_3.checkKeys=true := by decide +kernel
theorem keys45_4 : subtree45_4.checkKeys=true := by decide +kernel
theorem keys45_5 : subtree45_5.checkKeys=true := by decide +kernel
theorem keys45_6 : subtree45_6.checkKeys=true := by decide +kernel
theorem keys45_7 : subtree45_7.checkKeys=true := by decide +kernel
theorem keys45 : subtree45.checkKeys=true := by
  simp only [subtree45,Tree.checkKeys,keys45_0,keys45_1,keys45_2,keys45_3,keys45_4,keys45_5,keys45_6,keys45_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree45)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys45
