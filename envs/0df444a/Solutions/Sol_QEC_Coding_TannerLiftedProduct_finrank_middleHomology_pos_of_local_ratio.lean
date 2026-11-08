-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.finrank_middleHomology_pos_of_local_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:16:47.254976+00:00
-- url     : https://prove2.me/submissions/c199a119-18df-4775-aebb-bcbe7a4fc95d

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_qubitIndex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rate_le_finrank_middleHomology_of_local_ratio


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hW : 0 < Fintype.card W)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    0 < Module.finrank F (chainComplex label h h').middleHomology := by
  have hCardQ : 0 < Fintype.card
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) := by
    rw [card_qubitIndex]
    have hCardG : 0 < Fintype.card G := Fintype.card_pos
    positivity
  have hRate := rate_le_finrank_middleHomology_of_local_ratio
    label h h' rate hRatio
  have hLeftPositive : 0 < rate *
      (Fintype.card
        (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) : ℝ) :=
    mul_pos hRatePositive (Nat.cast_pos.mpr hCardQ)
  have hReal : 0 < (Module.finrank F
      (chainComplex label h h').middleHomology : ℝ) :=
    hLeftPositive.trans_le hRate
  exact_mod_cast hReal
end QEC.Coding.TannerLiftedProduct
