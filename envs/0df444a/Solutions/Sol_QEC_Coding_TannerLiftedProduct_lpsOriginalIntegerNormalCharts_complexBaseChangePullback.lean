-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalCharts_complexBaseChangePullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:59:56.226005+00:00
-- url     : https://prove2.me/submissions/f80c9caa-a3bd-477a-a563-81f02b4541f4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChanged


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) :
    let a := lpsOriginalIntegerNormalSchemeOverlapMap N hN false
    let b := lpsOriginalIntegerNormalSchemeOverlapMap N hN true
    let i := lpsOriginalIntegerNormalGluedChartMap N hN false
    let j := lpsOriginalIntegerNormalGluedChartMap N hN true
    let x := lpsOriginalIntegerNormalGluedToSpecZ N hN
    let t := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ))
    let h := lpsOriginalIntegerNormalCharts_pullback N hN
    IsPullback
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.firstOverlapOver a i x)).left)
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.secondOverlapOver a b i j x h)).left)
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.leftChartOver i x)).left)
      (((Over.pullback t).map
        (QEC.Coding.AlgebraicGeometry.ChartBaseChange.rightChartOver j x)).left) :=
  QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChanged
    (lpsOriginalIntegerNormalSchemeOverlapMap N hN false)
    (lpsOriginalIntegerNormalSchemeOverlapMap N hN true)
    (lpsOriginalIntegerNormalGluedChartMap N hN false)
    (lpsOriginalIntegerNormalGluedChartMap N hN true)
    (lpsOriginalIntegerNormalGluedToSpecZ N hN)
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
    (lpsOriginalIntegerNormalCharts_pullback N hN)
end QEC.Coding.TannerLiftedProduct
