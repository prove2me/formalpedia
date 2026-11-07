-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeInfty_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:48.124687+00:00
-- url     : https://prove2.me/submissions/c2a5914d-fe90-4081-a7a4-bd048e666edc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsModularForm_dilate_hasSum


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => (p:ℂ)*lpsModularDilationCoefficient
      (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n *
        Function.Periodic.qParam 1 (z:ℂ)^n)
      ((p:ℂ)*f (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • z)) := by
  have h := lpsModularForm_dilate_hasSum N p (Fact.out : p.Prime).pos (f : ModularForm _ 2) z
  have hcast : ((f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) : ℍ→ℂ)=
      (f:ℍ→ℂ) := rfl
  rw [hcast] at h
  have ht := h.mul_left (p:ℂ)
  apply ht.congr_fun
  intro n
  ring
end QEC.Coding.TannerLiftedProduct
