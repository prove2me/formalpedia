-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_square_le_adaptive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:22:48.712394+00:00
-- url     : https://prove2.me/submissions/064b1856-57a3-4b23-b99e-1dc083e9895a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_image_card_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^6) :
    (lpsTraceQuadraticShell q (r^2)).card ≤ 1600*(2*r/q^2+1)*K^5 := by
  classical
  have hf := Finset.card_le_mul_card_image (lpsTraceQuadraticShell q (r^2)) (800*K^5)
    (fun x _ => card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth q (r^2) K hq.pos hK hcap x)
  have hi := lpsTraceQuadraticShell_firstCoordinate_image_card_le q r hq hqr
  calc
    _ ≤ (800*K^5)*((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card := hf
    _ ≤ (800*K^5)*(2*(2*r/q^2+1)) := Nat.mul_le_mul_left _ hi
    _ = 1600*(2*r/q^2+1)*K^5 := by ring
end QEC.Coding.TannerLiftedProduct
