-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:30.309445+00:00
-- url     : https://prove2.me/submissions/2aeea754-166e-4620-949a-b52ec60b7a9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (n : ℕ) :
    iteratedFDeriv ℂ n (fun w => cexp (ℓ w)) =
      fun v => cexp (ℓ v) • (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
        (fun _ => ℓ) := by
  induction n with
  | zero =>
    funext v
    ext x
    simp [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  | succ n ih =>
    funext v
    ext x
    rw [iteratedFDeriv_succ_apply_left, ih]
    have hd : HasFDerivAt (fun w => cexp (ℓ w) •
        (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (fun _ => ℓ))
        ((cexp (ℓ v) • ℓ).smulRight
          ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (fun _ => ℓ))) v :=
      (ℓ.hasFDerivAt.cexp).smul_const _
    rw [hd.fderiv]
    simp [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn, Fin.prod_univ_succ, Fin.tail]
    all_goals ring
end ReciprocityTheory.ChartRestriction.G.I2
