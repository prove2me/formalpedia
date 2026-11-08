-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.labelledVertices_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:51:51.353242+00:00
-- url     : https://prove2.me/submissions/e1116b12-0ed4-4562-a593-201a86b98825

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_labelledVertices_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (L : Finset (VertexIndex G))
    (hL : IsClosedLabelledSet label c m L) :
    labelledVertices label c m ⊆ L := by
  intro v hv
  exact (mem_labelledVertices_iff label c m v).mp hv L hL
end QEC.Coding.TannerLiftedProduct
