-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.hasSum_CS_mul_t_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:31.47959+00:00
-- url     : https://prove2.me/submissions/43f16e22-aab8-4a27-9210-c2c3d540b691

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (c : ℕ → R) :
    letI := piTopS
    HasSum (fun k => CS (c k) * t ^ k) (PowerSeries.mk c) := by
  letI : TopologicalSpace R := piTop
  letI : TopologicalSpace S := piTopS
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_mk]
  apply (hasSum_ite_eq d (c d)).congr_fun
  intro i
  by_cases h : d = i
  · subst i
    simp
  · rw [if_neg h, if_neg (Ne.symm h)]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
