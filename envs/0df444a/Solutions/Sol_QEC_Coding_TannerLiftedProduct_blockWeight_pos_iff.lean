-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.blockWeight_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:56:50.60187+00:00
-- url     : https://prove2.me/submissions/bc2cfb24-1b32-495a-b957-5cfe56c71032

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_eq_zero_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    0 < blockWeight c ↔ c ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, blockWeight_eq_zero_iff]
end QEC.Coding.TannerLiftedProduct
