-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScalDeg.part_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:22.267096+00:00
-- url     : https://prove2.me/submissions/486d5d4a-2a48-475e-9fec-8a0de6488ced

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_prod_fiber
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_polD_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_gv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
open Classical
namespace PI.UnitaryGroupMassFormula.ScalDeg
theorem _root_.solution {T : Type} [Fintype T] {N N' : ℕ} (s s' : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (dg : T → ℕ) (hQ : HomDeg Q dg) (y' : T → Matrix (Fin N') (Fin N') ℂ) :
    polD (fun τ => s τ * s' τ) Q y' = C (∏ τ, s τ ^ dg τ) * polD s' Q y' := by
  rw [polD_eq, polD_eq]
  conv_lhs => rw [MvPolynomial.as_sum Q]
  conv_rhs => rw [MvPolynomial.as_sum Q]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [aeval_monomial, aeval_monomial]
  have hg : (v.prod fun i k => gv (fun τ => s τ * s' τ) y' i ^ k) =
      C (v.prod fun i k => s i.1 ^ k) * v.prod fun i k => gv s' y' i ^ k := by
    simp_rw [gv_mul, mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [map_finsuppProd]
    simp_rw [map_pow]
  have hp : (v.prod fun i k => s i.1 ^ k) = ∏ τ, s τ ^ dg τ := by
    rw [prod_fiber]
    exact Finset.prod_congr rfl fun τ _ => by rw [hQ v hv τ]
  rw [hg, hp]
  ring
end PI.UnitaryGroupMassFormula.ScalDeg
