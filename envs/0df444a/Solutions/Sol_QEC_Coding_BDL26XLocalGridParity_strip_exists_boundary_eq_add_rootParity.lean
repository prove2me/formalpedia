-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalGridParity.strip_exists_boundary_eq_add_rootParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:44:16.073636+00:00
-- url     : https://prove2.me/submissions/3cb94c81-f236-4b2e-9540-39411dc67fb6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_exists_graphBoundary_eq_add_rootParity


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalGridParity
open BDL26TannerLocalRegularity
open BDL26FiniteAlternatingCore
namespace QEC.Coding.BDL26XLocalGridParity
theorem _root_.solution
    (m : ℕ) (hm : 0 < m) (root : StripVertex m)
    (syndrome : Word (ZMod 2) (StripVertex m)) :
    ∃ correction : Word (ZMod 2) (StripEdge m),
      graphBoundary (stripStart m) (stripEnd m) correction =
        syndrome + Pi.single root (totalParity syndrome) :=
  exists_graphBoundary_eq_add_rootParity
    (stripStart m) (stripEnd m) root (stripPath m hm root) syndrome
end QEC.Coding.BDL26XLocalGridParity
