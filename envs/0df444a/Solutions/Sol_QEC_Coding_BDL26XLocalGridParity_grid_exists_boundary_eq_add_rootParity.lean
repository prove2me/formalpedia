-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalGridParity.grid_exists_boundary_eq_add_rootParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:44:32.316955+00:00
-- url     : https://prove2.me/submissions/a219d81e-0b96-45c1-a521-98965bc0ffb4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_exists_graphBoundary_eq_add_rootParity


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalGridParity
open BDL26TannerLocalRegularity
open BDL26FiniteAlternatingCore
namespace QEC.Coding.BDL26XLocalGridParity
theorem _root_.solution
    (m : ℕ) (hm : 0 < m) (root : GridVertex m)
    (syndrome : Word (ZMod 2) (GridVertex m)) :
    ∃ correction : Word (ZMod 2) (GridEdge m),
      graphBoundary (gridStart m) (gridEnd m) correction =
        syndrome + Pi.single root (totalParity syndrome) :=
  exists_graphBoundary_eq_add_rootParity
    (gridStart m) (gridEnd m) root (gridPath m hm root) syndrome
end QEC.Coding.BDL26XLocalGridParity
