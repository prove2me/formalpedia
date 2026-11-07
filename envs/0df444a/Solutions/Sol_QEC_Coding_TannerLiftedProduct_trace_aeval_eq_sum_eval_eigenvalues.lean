-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.trace_aeval_eq_sum_eval_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:35.003356+00:00
-- url     : https://prove2.me/submissions/43f7b4b3-55c7-4e20-8169-01f4fec9059f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace

set_option autoImplicit false
open Filter Asymptotics
open Polynomial
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (P : ℂ[X]) :
    LinearMap.trace ℂ E (aeval T P) =
      ∑ i : Fin (Module.finrank ℂ E),
        P.eval (hT.eigenvalues rfl i : ℂ) := by
  classical
  rw [LinearMap.trace_eq_sum_inner
    (aeval T P) (hT.eigenvectorBasis rfl)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Module.End.aeval_apply_of_hasEigenvector
    (hT.hasEigenvector_eigenvectorBasis rfl i)]
  rw [inner_smul_right, (hT.eigenvectorBasis rfl).inner_eq_one]
  simp
end QEC.Coding.TannerLiftedProduct
