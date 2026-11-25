-- Prove2me | solution 1 for PI.Dv.GLP.isIntegral_trace_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:19.489025+00:00
-- url     : https://prove2.me/submissions/272f8045-478f-4fca-bf7c-9aa8ebf6c470

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ArithmeticCylinders
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_IsIntegralTraceOfPow
import Theorems.Thm_PI_Dv_GLP_eigen_pow_eq_one
import Theorems.Thm_UpperTheory_Reformulated_B_ArithmeticCylinders_eigen_pow_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Polynomial
namespace PI.Dv.GLP
theorem _root_.solution {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace K W f) := by
  classical
  let b := Module.finBasis K W
  let L := AlgebraicClosure K
  let M := LinearMap.toMatrix b b f
  have hMn : M ^ n = 1 := by
    show LinearMap.toMatrix b b f ^ n = 1
    rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]
  let M' : Matrix _ _ L := M.map (algebraMap K L)
  have hM'n : M' ^ n = 1 := by
    have : M' ^ n = (M ^ n).map (algebraMap K L) :=
      (RingHom.map_pow (algebraMap K L).mapMatrix M n).symm
    rw [this, hMn]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have htr : algebraMap K L (LinearMap.trace K W f) = M'.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b]
    exact AddMonoidHom.map_trace (algebraMap K L) M
  have hint : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun μ hμ => ?_
    have h1 : μ ^ n = 1 := eigen_pow_eq_one M' n hM'n μ (Polynomial.isRoot_of_mem_roots hμ)
    exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  rw [← htr] at hint
  exact (isIntegral_algebraMap_iff (algebraMap K L).injective).1 hint
end PI.Dv.GLP
