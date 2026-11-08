-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_square_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:19.576014+00:00
-- url     : https://prove2.me/submissions/c830cec1-3b4d-4efb-843e-72bb3b9be0ac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceQuadraticShell_firstCoordinate_image_card_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^8) :
    (lpsTraceQuadraticShell q (r^2)).card ≤ 192*(2*r/q^2+1)*K^7 := by
  classical
  have hf := Finset.card_le_mul_card_image (lpsTraceQuadraticShell q (r^2)) (96*K^7)
    (fun x _ => card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh q (r^2) K hq.pos hK hcap x)
  have hi := lpsTraceQuadraticShell_firstCoordinate_image_card_le q r hq hqr
  calc
    _ ≤ (96*K^7)*((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card := hf
    _ ≤ (96*K^7)*(2*(2*r/q^2+1)) := Nat.mul_le_mul_left _ hi
    _ = 192*(2*r/q^2+1)*K^7 := by ring
end QEC.Coding.TannerLiftedProduct
