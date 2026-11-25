-- Prove2me | solution 1 for PI.QnRT.rdV_dz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:18.00915+00:00
-- url     : https://prove2.me/submissions/ae30823e-9003-4c47-842b-b4f361a0da23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_phi_diff
import Theorems.Thm_PI_QnRT_mul_exp_dz

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
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ : ℂ) :
    RdV (dz l κ (-star κ)) f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by
  have hφ := phi_diff l D f hf c hc g₁ hg₁ hD
  have hηd : HasDerivAt (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ)))
      (Pi.single l (c l * κ)) 0 := by
    rw [hasDerivAt_pi]
    intro i
    by_cases hi : i = l
    · subst hi
      simp only [Function.update_apply, if_true, Pi.single_eq_same]
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * κ)) κ 0 := by
        have h2 := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const κ).cexp).comp_ofReal
        simpa using h2
      simpa using h1.const_mul (c i)
    · simp only [Function.update_apply, hi, if_false, Pi.single_eq_of_ne hi]
      exact hasDerivAt_const _ _
  have hη0 : Function.update c l (c l * Complex.exp (((0 : ℝ) : ℂ) * κ)) = c := by simp
  have hcomp := hφ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hηd hη0.symm
  unfold RdV
  have hfun : (fun t : ℝ => f (w1 k r l (c l) * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)))) =
      (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) ∘
        (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ))) := by
    funext t
    rw [mul_exp_dz l (c l) κ g₁ hg₁ t]
    simp [Function.comp]
  rw [hfun, hcomp.deriv]
end PI.QnRT
