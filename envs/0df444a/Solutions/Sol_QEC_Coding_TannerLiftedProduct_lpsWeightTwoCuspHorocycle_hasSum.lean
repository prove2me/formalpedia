-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCuspHorocycle_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:17:43.758707+00:00
-- url     : https://prove2.me/submissions/26cdc00d-c036-412e-9ebd-81bfeb72b695

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      (Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ))^n)
      (f (lpsHorocyclePoint y hy x)) := by
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  let : Fact (IsCusp OnePoint.infty
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods (by norm_num) hp⟩
  exact ModularForm.hasSum_qExpansion f (by norm_num) hp _
end QEC.Coding.TannerLiftedProduct
