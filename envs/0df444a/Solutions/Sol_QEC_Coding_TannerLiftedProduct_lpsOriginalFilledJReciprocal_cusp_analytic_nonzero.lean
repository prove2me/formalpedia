-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_analytic_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:13:25.102336+00:00
-- url     : https://prove2.me/submissions/50d0553d-2f41-41ff-961e-4288ea9b4f95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_nonzero_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_analytic_nonzero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 4∣N) (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let e := lpsOriginalFilledCuspChart N c
  obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c ⟨z,hz⟩ hz0
  have hn : lpsOriginalFilledJ N (e.symm z)-a≠0 := by
    rw [show e.symm z=Sum.inl (lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ) from hτ]
    change lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ
      (lpsOriginalCuspRepresentative N c) •τ.val)-a≠0
    exact sub_ne_zero.mpr (ho _)
  have hf := ((lpsOriginalFilledJ_cusp_analytic_nonzero N hN c z hz hz0).sub
    analyticAt_const).inv hn
  apply hf.congr
  have ht : ∀ᶠ w in 𝓝 z, w∈e.target := e.open_target.mem_nhds hz
  have hnz : ∀ᶠ w in 𝓝 z, w≠0 := IsOpen.mem_nhds isOpen_compl_singleton hz0
  filter_upwards [ht,hnz] with w hwt hw0
  exact (lpsOriginalFilledJReciprocal_cusp_nonzero_eq N a c ⟨w,hwt⟩ hw0).symm
end QEC.Coding.TannerLiftedProduct
