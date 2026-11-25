-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_hasDerivAt_invpow__0b9fd55a1697
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:10.360042+00:00
-- url     : https://prove2.me/submissions/49f94898-d6d9-40e9-b045-f3eef70210db

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetClassEstimate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) {a : ℕ} (h0 : a = 0 ∨ c 0 ≠ 0) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by
  cases a with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | succ n =>
    have hc0 : c 0 ≠ 0 := h0.resolve_left (Nat.succ_ne_zero n)
    have h2 := ((hasDerivAt_inv hc0).pow (n + 1)).comp (0 : ℝ) hc
    have h3 : HasDerivAt (fun t => (c t)⁻¹ ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (c 0)⁻¹ ^ (n + 1 - 1) * -(c 0 ^ 2)⁻¹ * c') 0 := h2
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring
end Formalism.FourierDecayAlt.P.MinorPolynomials
