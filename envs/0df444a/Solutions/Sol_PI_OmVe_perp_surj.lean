-- Prove2me | solution 1 for PI.OmVe.perp_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:01.476461+00:00
-- url     : https://prove2.me/submissions/f4709c37-acc8-4ffc-a15b-587cd00d5e43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_FfHSelfOfSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))
namespace PI.OmVe
theorem _root_.solution {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) (w : Fin a' → k × k) :
    ∃ x : Fin M → k × k, ∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = w j := by
  classical
  set c := T0⁻¹.mulVec w with hc
  refine ⟨fun l => ∑ m, Y m l * c m, fun j => ?_⟩

  have h1 : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j)
      (fun l => ∑ m, Y m l * c m) = ∑ m, T0 j m * c m := by
    rw [← hY]
    simp only [ffGram, ffH, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h1]
  have h2 : T0.mulVec c = w := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h3 := congrFun h2 j
  simpa [Matrix.mulVec, dotProduct] using h3
end PI.OmVe
