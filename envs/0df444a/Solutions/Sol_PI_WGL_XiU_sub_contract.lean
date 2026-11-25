-- Prove2me | solution 1 for PI.WGL.XiU.sub_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:45.259912+00:00
-- url     : https://prove2.me/submissions/30909abd-c532-421d-aa12-624f3181def8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Theorems.Thm_PI_WGL_XiU_normSq_sum_mulVec
import Theorems.Thm_PI_WGL_XiU_sum_comp_le
import Theorems.Thm_PI_WGL_XiU_sum_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix
namespace PI.WGL.XiU
theorem _root_.solution {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I J : Fin s → Fin N) (hI : Function.Injective I) (hJ : Function.Injective J) (v : Fin s → ℂ) :
    ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p) ≤ ∑ q, Complex.normSq (v q) := by
  set w : Fin N → ℂ := Function.extend J v 0 with hw
  have hwJ : ∀ q, w (J q) = v q := fun q => hJ.extend_apply v 0 q
  have hw0 : ∀ b, b ∉ Set.range J → w b = 0 := by
    intro b hb
    rw [hw, Function.extend_apply' _ _ _ hb]
    rfl
  have hmv : ∀ p, ((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p = (x *ᵥ w) (I p) := by
    intro p
    have hs := sum_comp_eq J hJ (fun b => x (I p) b * w b) (fun b hb => by simp [hw0 b hb])
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [hs]
    simp only [hwJ]
  have hnorm : ∑ b, Complex.normSq (w b) = ∑ q, Complex.normSq (v q) := by
    have hs := sum_comp_eq J hJ (fun b => Complex.normSq (w b)) (fun b hb => by simp [hw0 b hb])
    rw [hs]
    simp only [hwJ]
  calc ∑ p, Complex.normSq (((Matrix.of fun p q => x (I p) (J q)) *ᵥ v) p)
      = ∑ p, Complex.normSq ((x *ᵥ w) (I p)) := by simp only [hmv]
    _ ≤ ∑ a, Complex.normSq ((x *ᵥ w) a) :=
        sum_comp_le I hI _ (fun a => Complex.normSq_nonneg _)
    _ = ∑ b, Complex.normSq (w b) := normSq_sum_mulVec x hx w
    _ = ∑ q, Complex.normSq (v q) := hnorm
end PI.WGL.XiU
