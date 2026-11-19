-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_cpow_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:28:13.244463+00:00
-- url     : https://prove2.me/submissions/4dffc553-edd4-4ffe-a41f-ea777d1ef432

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_rpow_integrable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) : IntegrableOn (fun τ : ℍ => (lpsCuspPeterssonDensity N f τ:ℂ)*(τ.im:ℂ)^s)
      ModularGroup.fd := by
  have hi := lpsCuspPeterssonDensity_rpow_integrable N f s.re
  refine hi.mono' ?_ ?_
  · have hc : Continuous (fun τ : ℍ => (lpsCuspPeterssonDensity N f τ:ℂ)*(τ.im:ℂ)^s) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.comp (lpsCuspPeterssonDensity_continuous N f)
      · apply continuous_iff_continuousAt.mpr
        intro τ
        exact (Complex.continuousAt_ofReal_cpow_const τ.im s (Or.inr τ.im_ne_zero)).comp
          continuous_im.continuousAt
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun τ => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (lpsCuspPeterssonDensity_nonneg N f τ),
        Complex.norm_cpow_eq_rpow_re_of_pos τ.im_pos])
end QEC.Coding.TannerLiftedProduct
