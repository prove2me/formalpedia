-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_rpow_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:27:14.543954+00:00
-- url     : https://prove2.me/submissions/1c7418b0-976c-4bc4-b4e2-b6d4cef5e3d2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_rpow_isBigO
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_fundamentalDomain_volume_finite
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℝ) : IntegrableOn (fun τ => lpsCuspPeterssonDensity N f τ*τ.im^s) ModularGroup.fd := by
  have hc : Continuous (fun τ : ℍ => lpsCuspPeterssonDensity N f τ*τ.im^s) :=
    (lpsCuspPeterssonDensity_continuous N f).mul
      (continuous_im.rpow_const (fun τ => Or.inl τ.im_ne_zero))
  have hO : (fun τ : ℍ => lpsCuspPeterssonDensity N f τ*τ.im^s)=O[atImInfty]
      (fun τ => τ.im^(0:ℝ)) := by
    simpa using lpsCuspPeterssonDensity_rpow_isBigO N f s
  obtain ⟨C,hC⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hc hO
  have hi : IntegrableOn (fun _ : ℍ => C) ModularGroup.fd :=
    integrableOn_const (ne_of_lt lpsPetersson_fundamentalDomain_volume_finite)
  refine hi.mono' hc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with τ hτ
  simpa only [Real.rpow_zero,mul_one] using hC τ hτ
end QEC.Coding.TannerLiftedProduct
