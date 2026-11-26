-- Prove2me | solution 1 for adjoint_aeval_apply_of_forall_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:58.4577+00:00
-- url     : https://prove2.me/submissions/3819e193-aa4d-4223-a883-9e64444f87b0

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem _root_.solution (T : E →L[ℂ] E) (V : E →L[ℂ] H) (U : H →L[ℂ] H)
    (hpow : ∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x) (p : ℂ[X]) (x : E) :
    adjoint V ((aeval U p) (V x)) = (aeval T p) x := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [sum_apply, smul_apply, map_sum, map_smul, hpow]
