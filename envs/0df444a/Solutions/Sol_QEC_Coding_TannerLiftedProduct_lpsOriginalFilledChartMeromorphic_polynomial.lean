-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:34:34.574685+00:00
-- url     : https://prove2.me/submissions/5561b2ca-96f5-400e-b461-5806f2341d43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (P : Polynomial ℂ) :
    lpsOriginalFilledChartMeromorphic N hN (fun x => P.eval (F x)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : (fun x => (P+Q).eval (F x)) =
        ((fun x => P.eval (F x)) + (fun x => Q.eval (F x))) := by
      funext x
      exact Polynomial.eval_add
    rw [he]
    exact lpsOriginalFilledChartMeromorphic_add N hN hP hQ
  | monomial m c =>
    have he : (fun x => (Polynomial.monomial m c).eval (F x)) =
        ((fun _ => c) * F^m) := by
      funext x
      exact Polynomial.eval_monomial
    rw [he]
    exact lpsOriginalFilledChartMeromorphic_mul N hN
      (lpsOriginalFilledChartMeromorphic_const N hN c)
      (lpsOriginalFilledChartMeromorphic_pow N hN hF m)
end QEC.Coding.TannerLiftedProduct
