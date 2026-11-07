-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:41.033431+00:00
-- url     : https://prove2.me/submissions/48b849ca-bb54-4540-b4b9-13e5e6599f2b

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (y : ℝ) (hy : 0<y) (x : ℝ) :
    (lpsHorocyclePoint y hy x).im=y := rfl
end QEC.Coding.TannerLiftedProduct
