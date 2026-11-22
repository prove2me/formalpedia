-- Prove2me | solution 1 for Paper.Hypergraph.main_width_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:08.228555+00:00
-- url     : https://prove2.me/submissions/3726ed7e-3521-4211-9b62-a8df1ad286dc

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
import Theorems.Thm_Paper_Hypergraph_balanced_rounding
import Theorems.Thm_Paper_Hypergraph_main_width_comparison_of_rounding


set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution : MainWidthComparison :=
  main_width_comparison_of_rounding balanced_rounding
end Paper.Hypergraph
