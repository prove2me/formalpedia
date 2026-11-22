-- Prove2me | solution 1 for P2M_ProbabilityTheory_Kernel_compProd_assoc__371caf64c88a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:21.85137+00:00
-- url     : https://prove2.me/submissions/3d3a0b8b-ddda-41df-bedd-cd68fb8c0e66

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
namespace ProbabilityTheory.Kernel
theorem _root_.solution (ξ : Kernel T S) [IsSFiniteKernel ξ]
    (κ : Kernel (T × S) U) [IsSFiniteKernel κ] (η :
      Kernel (T × S × U) V) [IsSFiniteKernel η] :
    map ((ξ ⊗ₖ κ) ⊗ₖ η) MeasurableEquiv.prodAssoc
      = ξ ⊗ₖ
        (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)) := by
  ext x s hs
  rw [map_apply' _ (by fun_prop) _ hs,
    compProd_apply (MeasurableEquiv.prodAssoc.measurable hs),
    compProd_apply hs, lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' (MeasurableEquiv.prodAssoc.measurable hs) _
  congr with a
  rw [compProd_apply]
  swap; · exact measurable_prodMk_left hs
  congr
end ProbabilityTheory.Kernel
