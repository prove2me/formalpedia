-- Prove2me | solution 1 for P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:22.209202+00:00
-- url     : https://prove2.me/submissions/62f75f46-82de-48d9-9081-4d7fe25f6ee2

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    followOrder? choices (Forest.empty V) order.val =
      some (grownForestForSupportOrder choices I order) :=
  (Classical.choose_spec
    (exists_followOrder?_eq_some_support_of_mem_edgeSetOrders
      choices order.property)).1
end BKAR.Forest
