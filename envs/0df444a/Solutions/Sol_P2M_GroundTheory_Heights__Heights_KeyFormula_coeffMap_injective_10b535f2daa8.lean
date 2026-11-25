-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_coeffMap_injective_10b535f2daa8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:22.28984+00:00
-- url     : https://prove2.me/submissions/867879bd-c89f-4ea6-a3a9-40cc72757a03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_quasiPeriodic_eq_zero_46166fd09bf9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_fn_eq_line_d80249d70c44

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : Function.Injective coeffMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨f, hf⟩ h0
  obtain ⟨hd, hper, haut⟩ := id hf
  set F : ℂ → ℂ := fun w => f (fun _ => w) with hF
  have hFd : Differentiable ℂ F := hd.comp (differentiable_pi.2 fun _ => differentiable_id)
  have h1 : ∀ w, F (w + 1) = F w := by
    intro w
    have := hper (fun _ => 1) (fun _ => w)
    have hp : perFactor (HalfChar.zero 1) 3 (fun _ => 1) = 1 := by
      simp [perFactor, HalfChar.a, HalfChar.zero, dotProduct]
    rw [hp, one_mul] at this
    simp only [hF]
    convert this using 2
    funext i; simp [intVec]
  have h2 : ∀ w, F (w + I) = cexp (-(π * I * 3 * I)) * cexp (-2 * π * I * (3 : ℕ) * w) * F w := by
    intro w
    have := haut (fun _ => 1) (fun _ => w)
    simp only [hF]
    have hz : (fun _ : Fin 1 => w) + tauI.τ *ᵥ intVec (fun _ => 1) = fun _ => w + I := by
      funext i; fin_cases i; simp [tauI, Matrix.mulVec, dotProduct, intVec]
    rw [hz] at this
    rw [this, ← Complex.exp_add]
    congr 2
    simp [autFactor, tauI, Matrix.mulVec, dotProduct, intVec, HalfChar.b, HalfChar.zero]
    ring_nf
  have hzero : F = 0 := by
    refine quasiPeriodic_eq_zero 3 (by norm_num) F hFd _ (Complex.exp_ne_zero _) h1 h2 ?_
    intro k hk
    have := congrFun h0 ⟨k, hk⟩
    simpa [coeffMap, hF] using this
  apply Subtype.ext
  funext z
  show f z = 0
  rw [fn_eq_line f z]
  exact congrFun hzero (z 0)
end GroundTheory.Heights₂.Heights.KeyFormula
