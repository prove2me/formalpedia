-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFixedPoint_trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:10.705359+00:00
-- url     : https://prove2.me/submissions/a2aa1a16-9704-4b69-906d-cc47289494ae

import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g : GL (Fin 2) ℝ) (hdet : g.val.det=1)
    (τ : ℍ) (hfix : g • τ=τ) :
    g.val.trace^2+4*(g 1 0)^2*τ.im^2=4 := by
  have hq := (UpperHalfPlane.gl_smul_eq_self_iff_quadratic (by rw [hdet];norm_num)).mp hfix
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp [Complex.mul_re,Complex.mul_im] at hre him
  have hdiag : 2*(g 1 0)*τ.re+g 1 1-g 0 0=0 := by
    have hm : (2*(g 1 0)*τ.re+g 1 1-g 0 0)*τ.im=0 := by nlinarith [him]
    exact (mul_eq_zero.mp hm).resolve_right τ.im_ne_zero
  have hr := congrArg (fun x : ℝ => (g 1 0)*x) hre
  have hi := congrArg (fun x : ℝ => (g 1 0)*τ.re*x) hdiag
  have hs := congrArg (fun x : ℝ => x^2) hdiag
  rw [Matrix.trace_fin_two]
  rw [Matrix.det_fin_two] at hdet
  nlinarith [hr,hi,hs]
end QEC.Coding.TannerLiftedProduct
