-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.dgl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:36.516303+00:00
-- url     : https://prove2.me/submissions/8039040b-9cb4-478c-92e0-80c8651a0a64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_rev_eq_c_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Hpk_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution {u : ℂ} (hu : (starRingEnd ℂ) u * u = 1) : dgl r u ∈ UWb 0 r := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · show (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r
    ext p q
    simp only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]
    rw [Hpk_apply]
    by_cases hq : q = Fin.rev p
    · subst hq
      by_cases hp : p = cI r
      · subst hp
        have hc : Fin.rev (cI r) = cI r := (rev_eq_c_iff _).2 rfl
        simp only [hc, if_true]
        show star u * -1 * u = -1
        rw [show star u = (starRingEnd ℂ) u from rfl]
        linear_combination -hu
      · have hc : Fin.rev p ≠ cI r := fun h => hp ((rev_eq_c_iff p).1 h)
        simp [hp, hc]
    · simp [hq]
  · have hne : eI 0 r a ≠ cI r := by
      intro h
      have := congrArg Fin.val h
      simp [eI, cI] at this
      omega
    simp only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]
  · have hne : esI 0 r a ≠ cI r := by
      intro h
      have := congrArg Fin.val h
      simp [esI, cI] at this
      omega
    simp only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]
end PI.ExistsGaugeMeasureForEachRank.W
