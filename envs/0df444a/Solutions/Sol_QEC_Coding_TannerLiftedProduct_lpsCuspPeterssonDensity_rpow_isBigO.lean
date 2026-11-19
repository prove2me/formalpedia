-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_rpow_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:26:15.837144+00:00
-- url     : https://prove2.me/submissions/3d135e51-e5da-4837-8a27-f4d90cedbd10

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_exp_decay
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℝ) : (fun τ => lpsCuspPeterssonDensity N f τ*τ.im^s)=O[atImInfty]
      (fun _ => (1:ℝ)) := by
  obtain ⟨a,ha,hb⟩ := lpsCuspPeterssonDensity_exp_decay N f
  have hexp : (fun τ : ℍ => Real.exp (-a*τ.im)*τ.im^s)=O[atImInfty]
      (fun _ => (1:ℝ)) := by
    have h := (isLittleO_exp_mul_rpow_of_lt s (show -a<(0:ℝ) by linarith)).isBigO
    simpa only [zero_mul,Real.exp_zero,Function.comp_def,atImInfty] using h.comp_tendsto (tendsto_comap :
      Tendsto UpperHalfPlane.im atImInfty atTop)
  exact (hb.mul (isBigO_refl (fun τ : ℍ => τ.im^s) atImInfty)).trans hexp
end QEC.Coding.TannerLiftedProduct
