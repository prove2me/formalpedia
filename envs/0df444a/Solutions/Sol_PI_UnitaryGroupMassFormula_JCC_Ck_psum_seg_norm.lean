-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.JCC.Ck.psum_seg_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:20.210715+00:00
-- url     : https://prove2.me/submissions/cb8a5e48-60ae-493f-ba57-524e13b0a9a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PCkPartials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC PI.UnitaryGroupMassFormula.JCC.Ck
variable {d : ℕ}
namespace PI.UnitaryGroupMassFormula.JCC.Ck
theorem _root_.solution (y h : Fin d → ℝ) (i : Fin d) {s : ℝ} (hs : |s| ≤ |h i|) :
    ‖psum y h i.val + s • Pi.single i (1 : ℝ) - y‖ ≤ ‖h‖ := by
  have hv : ∀ l, ((psum y h i.val + s • Pi.single i (1 : ℝ) - y : Fin d → ℝ) l) =
      (if l.val < i.val then h l else 0) + s * ((Pi.single i (1 : ℝ) : Fin d → ℝ) l) := by
    intro l
    simp only [psum, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).mpr (fun l => ?_)
  rw [hv l]
  by_cases hl : l = i
  · subst hl
    rw [if_neg (lt_irrefl _), Pi.single_eq_same, zero_add, mul_one, Real.norm_eq_abs]
    exact hs.trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h l)
  · rw [Pi.single_eq_of_ne hl, mul_zero, add_zero]
    split_ifs
    · exact norm_le_pi_norm h l
    · rw [norm_zero]
      exact norm_nonneg h
end PI.UnitaryGroupMassFormula.JCC.Ck
