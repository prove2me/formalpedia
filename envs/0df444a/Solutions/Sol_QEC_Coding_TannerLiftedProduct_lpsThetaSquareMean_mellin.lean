-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:33:33.11915+00:00
-- url     : https://prove2.me/submissions/d6237186-f0e0-4e88-8a0b-fdcd2b3a352c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleSquareMean_mellin


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (s : ℂ) (hs : 2<s.re) :
    mellin (fun y : ℝ => (lpsThetaSquareMean q hq4 y:ℂ)) s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)) s := by
  have : NeZero ((4*q)^2) := ⟨by have hq := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspHorocycleSquareMean_mellin _ _ _ hs
end QEC.Coding.TannerLiftedProduct
