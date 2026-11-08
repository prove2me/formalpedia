-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.boundary1_apply_eq_sum_supportCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:54.732504+00:00
-- url     : https://prove2.me/submissions/eea9ca20-d90b-4b70-8655-07d073cc0944

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1Matrix_eq_zero_of_not_mem_supportCover

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G) :
    LiftedProduct.boundary1 (data label h h') c c0 =
      ∑ q ∈ boundary1SupportCover label h h' c0,
        LiftedProduct.boundary1Matrix (data label h h') c0 q * c q := by
  classical
  change (∑ q, LiftedProduct.boundary1Matrix (data label h h') c0 q * c q) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _hqUniv hqCover
  rw [boundary1Matrix_eq_zero_of_not_mem_supportCover
    label h h' c0 q hqCover, zero_mul]
end QEC.Coding.TannerLiftedProduct
