-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.labelledVertices_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:54:28.661466+00:00
-- url     : https://prove2.me/submissions/5402292b-8f3b-443c-8832-25521fbf6831

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_labelledVertices_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_subset

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
    (m : Nat) :
    IsClosedLabelledSet label c m (labelledVertices label c m) := by
  constructor
  · intro v hv
    rw [mem_labelledVertices_iff]
    intro L hL
    exact hL.1 hv
  · intro v hvIncident hvDegree
    rw [mem_labelledVertices_iff]
    intro L hL
    apply hL.2 v hvIncident
    exact hvDegree.trans (Finset.sum_le_sum_of_subset
      (labelledVertices_subset label c m L hL))
end QEC.Coding.TannerLiftedProduct
