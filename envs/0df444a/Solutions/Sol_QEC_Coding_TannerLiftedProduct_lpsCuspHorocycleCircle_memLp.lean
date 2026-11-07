-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:25.354965+00:00
-- url     : https://prove2.me/submissions/3a907f48-ac97-4f78-85e1-e70ca79e8898

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_continuous

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    MemLp (lpsCuspHorocycleCircle N f y) 2 (@AddCircle.haarAddCircle 1 ⟨by norm_num⟩) :=
  (lpsCuspHorocycleCircle_continuous N f y hy).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
end QEC.Coding.TannerLiftedProduct
