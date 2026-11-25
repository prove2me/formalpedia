-- Prove2me | solution 1 for PI.DefPosDefWork.posDef_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:08.91896+00:00
-- url     : https://prove2.me/submissions/0c05267a-d2b5-4488-b247-9b1ebe9f704d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_PositiveDefiniteSecond
import Theorems.Thm_PI_DefPosDefWork_re_nonneg_of_rat
import Theorems.Thm_PI_DefPosDefWork_re_quad

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
theorem _root_.solution {E : Type} [Field E] (φ : E →+* ℂ) {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ)
    (hN : N.IsHermitian) (hu : IsUnit N) (hNr : (∀ t : E, (φ t).im = 0) → ∀ i j, (N i j).im = 0)
    (hpt : ∀ x : Fin k → E, 0 ≤ (star (fun i => φ (x i)) ⬝ᵥ (N *ᵥ (fun i => φ (x i)))).re) : N.PosDef := by
  haveI : CharZero E := RingHom.charZero φ
  have hPSD : ∀ v : Fin k → ℂ, 0 ≤ (star v ⬝ᵥ (N *ᵥ v)).re := by
    by_cases hreal : ∀ t : E, (φ t).im = 0
    · have hNr' := hNr hreal
      have hQc : Continuous fun a : Fin k → ℝ =>
          (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re := by
        show Continuous fun a : Fin k → ℝ => (∑ i, star ((a i : ℂ)) * ∑ j, N i j * (a j : ℂ)).re
        exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ =>
          (continuous_star.comp (Complex.continuous_ofReal.comp (continuous_apply i))).mul
            (continuous_finset_sum _ fun j _ =>
              continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))))
      have hd : DenseRange (fun α : Fin k → ℚ => fun i => (α i : ℝ)) :=
        DenseRange.piMap fun _ => Rat.denseRange_cast
      have hreal' : ∀ a : Fin k → ℝ, 0 ≤ (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re :=
        fun a => hd.induction_on a (isClosed_le continuous_const hQc) (fun α => by
          have h1 := hpt (fun i => (α i : E))
          simpa [map_ratCast] using h1)
      intro v
      have e := re_quad N hNr' (fun i => (v i).re) (fun i => (v i).im)
      have hv : (fun i => ((v i).re : ℂ) + ((v i).im : ℂ) * Complex.I) = v :=
        funext fun i => Complex.re_add_im (v i)
      rw [hv] at e
      rw [e]
      exact add_nonneg (hreal' _) (hreal' _)
    · push_neg at hreal
      obtain ⟨t, ht⟩ := hreal
      refine re_nonneg_of_rat N (φ t) ht (fun α β => ?_)
      have h1 := hpt (fun i => (α i : E) + (β i : E) * t)
      simpa [map_add, map_mul, map_ratCast] using h1
  have hpsd : N.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hN, fun v => ?_⟩
    rw [Complex.nonneg_iff]
    exact ⟨hPSD v, (hN.im_star_dotProduct_mulVec_self v).symm⟩
  exact hpsd.posDef_iff_isUnit.2 hu
end PI.DefPosDefWork
