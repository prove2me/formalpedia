-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rate_le_finrank_middleHomology_of_local_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:18:10.703368+00:00
-- url     : https://prove2.me/submissions/48859d35-4d7e-48b5-aafc-851790bfaa1e

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_c0Index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_c2Index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_chainComplex_middle_card
import Theorems.Thm_QEC_Coding_LiftedProduct_rate_le_finrank_middleHomology_of_endpoint_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    rate * Fintype.card
        (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) ≤
      (Module.finrank F
        (LiftedProduct.chainComplex (data label h g')).middleHomology : ℝ) := by
  apply LiftedProduct.rate_le_finrank_middleHomology_of_endpoint_bound
    (data label h g') rate
  rw [card_c0Index (G := G) (W := W) (R := R),
    card_c2Index (G := G) (W := W) (R' := R'),
    chainComplex_middle_card (G := G) (W := W) (R := R) (R' := R')]
  calc
    ((2 * Fintype.card R * Fintype.card W * Fintype.card G : Nat) : ℝ) +
        ((2 * Fintype.card R' * Fintype.card W * Fintype.card G : Nat) : ℝ) =
      (Fintype.card G : ℝ) *
        (2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W) := by
          push_cast
          ring
    _ ≤ (Fintype.card G : ℝ) *
        ((1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :=
      mul_le_mul_of_nonneg_left hRatio (Nat.cast_nonneg _)
    _ = (1 - rate) *
        (Fintype.card G *
          (Fintype.card W ^ 2 + 4 * Fintype.card R * Fintype.card R') : Nat) := by
      push_cast
      ring
end QEC.Coding.TannerLiftedProduct
