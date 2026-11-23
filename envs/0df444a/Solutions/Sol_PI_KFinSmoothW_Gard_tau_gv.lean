-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.tau_gv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:01.96051+00:00
-- url     : https://prove2.me/submissions/a512d79d-02e3-4bbd-8c9f-030f35e7011c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
import Theorems.Thm_PI_KFinSmoothW_Gard_umat_closedEmb
import Theorems.Thm_PI_KFinSmoothW_Gard_umat_mem
import Theorems.Thm_PI_KFinSmoothW_Gard_integrable_orbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
namespace PI.KFinSmoothW.Gard
theorem _root_.solution {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (x : H)
    (γ : UJ ε) :
    τ (umat γ) (gv ε τ Φ x) =
      ∫ h, Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h) • τ (umat h) x ∂(muG ε) := by
  have hint := integrable_orbit hτ (fun h => Φ (umat h)) (hΦ.comp (continuous_coeMatrix ε))
    (hΦc.comp_isClosedEmbedding (umat_closedEmb ε)) x
  rw [gv, ← (τ (umat γ)).integral_comp_comm hint]
  have key := integral_mul_left_eq_self (μ := muG ε)
    (fun h' => Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h') • τ (umat h') x) γ
  beta_reduce at key
  rw [← key]
  congr 1
  funext h
  rw [show umat (γ * h) = umat γ * umat h from rfl, ← Matrix.mul_assoc,
    coeMatrix_left_inv ε _ (umat_mem γ), Matrix.one_mul, hτ.1.2 _ (umat_mem γ) _ (umat_mem h), map_smul]
  rfl
end PI.KFinSmoothW.Gard
