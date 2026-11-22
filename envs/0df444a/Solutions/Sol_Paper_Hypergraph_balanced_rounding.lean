-- Prove2me | solution 1 for Paper.Hypergraph.balanced_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:13.981844+00:00
-- url     : https://prove2.me/submissions/77821e45-7dc8-4629-bd82-0efb31c990eb

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
import Theorems.Thm_Paper_Hypergraph_twoTerminal_rounding
import Theorems.Thm_Paper_Hypergraph_balancedRounding_of_twoTerminalRounding


set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution : BalancedRounding :=
  balancedRounding_of_twoTerminalRounding twoTerminal_rounding
end Paper.Hypergraph
