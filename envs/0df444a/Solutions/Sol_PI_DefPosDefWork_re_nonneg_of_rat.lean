-- Prove2me | solution 1 for PI.DefPosDefWork.re_nonneg_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:43.706378+00:00
-- url     : https://prove2.me/submissions/37f6dd42-d1a4-487b-b51a-63ec2da851a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_PositiveDefiniteSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder
namespace PI.DefPosDefWork
theorem _root_.solution {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ α β : Fin k → ℚ, 0 ≤ (star (fun i => (α i : ℂ) + (β i : ℂ) * z) ⬝ᵥ
      (M *ᵥ (fun i => (α i : ℂ) + (β i : ℂ) * z))).re)
    (v : Fin k → ℂ) : 0 ≤ (star v ⬝ᵥ (M *ᵥ v)).re := by
  have hQc : Continuous fun w : Fin k → ℂ => (star w ⬝ᵥ (M *ᵥ w)).re := by
    show Continuous fun w : Fin k → ℂ => (∑ i, star (w i) * ∑ j, M i j * w j).re
    exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ =>
      (continuous_star.comp (continuous_apply i)).mul
        (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)))
  let ψ : (Fin k → ℝ) × (Fin k → ℝ) → (Fin k → ℂ) := fun p i => (p.1 i : ℂ) + (p.2 i : ℂ) * z
  have hψ : Continuous ψ := by fun_prop
  let d : (Fin k → ℚ) × (Fin k → ℚ) → (Fin k → ℝ) × (Fin k → ℝ) :=
    Prod.map (fun α i => (α i : ℝ)) (fun β i => (β i : ℝ))
  have hd : DenseRange d :=
    (DenseRange.piMap fun _ => Rat.denseRange_cast).prodMap (DenseRange.piMap fun _ => Rat.denseRange_cast)
  have key : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), 0 ≤ (star (ψ p) ⬝ᵥ (M *ᵥ ψ p)).re := fun p =>
    hd.induction_on p (isClosed_le continuous_const (hQc.comp hψ)) (fun q => by simpa [ψ, d] using h q.1 q.2)
  let p : (Fin k → ℝ) × (Fin k → ℝ) := (fun i => (v i).re - (v i).im / z.im * z.re, fun i => (v i).im / z.im)
  have hp : ψ p = v := by
    funext i
    apply Complex.ext <;> simp [ψ, p] <;> (try field_simp) <;> (try ring)
  have h1 := key p
  rwa [hp] at h1
end PI.DefPosDefWork
