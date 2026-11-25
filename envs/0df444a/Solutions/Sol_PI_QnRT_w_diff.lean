-- Prove2me | solution 1 for PI.QnRT.w_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:13.130245+00:00
-- url     : https://prove2.me/submissions/15ef6ee0-4b8d-4e9f-8530-411cd3ce0e05

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_w_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) (g₁ : Mx k r) (c : Fin r → ℂ) (hc : c l ≠ 0) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) c := by
  have hfun : (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) = fun c' : Fin r → ℂ =>
      (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) +
        (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ)) * g₁ := by
    funext c'
    rw [w_decomp]
  rw [hfun]
  have h1 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => c' l) c := differentiableAt_apply l c
  have hs : DifferentiableAt ℝ (fun c' : Fin r → ℂ => star (c' l)) c :=
    Complex.conjCLE.differentiableAt.comp c h1
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (star (c' l))⁻¹) c :=
    hs.inv (by simpa using hc)
  have hin : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) +
        (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ) : Mx k r)) c :=
    ((differentiableAt_const _).add (h1.smul_const _)).add (h2.smul_const _)
  let Lm : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g₁)
  exact Lm.differentiableAt.comp c hin
end PI.QnRT
