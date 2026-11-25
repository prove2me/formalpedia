-- Prove2me | solution 1 for PI.EF.Lent_disc_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:22.495997+00:00
-- url     : https://prove2.me/submissions/1a4c21be-05ed-4bcd-99ab-98bf7415b6de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_Lent_bound
import Theorems.Thm_PI_EF_ctr_re
import Theorems.Thm_PI_EF_ctr_im
import Theorems.Thm_PI_EF_half_le_norm_Lent_ctr
import Theorems.Thm_PI_EF_le_exp_Mfun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_re
attribute [local simp] PI.EF.ctr_im

set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C) (hI : PI.LInvRight)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (t : ℝ) :
    ∀ z ∈ closedBall (ctr t) 6, ‖Lent χ z‖ ≤ Real.exp (Mfun A C N t) * ‖Lent χ (ctr t)‖ := by
  intro z hz
  have hz' : ‖z - ctr t‖ ≤ 6 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - ctr t)).trans hz'
  have him := (Complex.abs_im_le_norm (z - ctr t)).trans hz'
  rw [Complex.sub_re, ctr_re] at hre
  rw [Complex.sub_im, ctr_im] at him
  have h1 : -4 ≤ z.re := by linarith [neg_abs_le (z.re - 2)]
  have h2 : z.re ≤ 8 := by linarith [le_abs_self (z.re - 2)]
  have h3 : |z.im| ≤ |t| + 6 := by
    have := abs_sub_abs_le_abs_sub z.im t
    linarith
  have hb := Lent_bound hA hC hG hχ h1 h2 h3
  have he := le_exp_Mfun (A := A) hC N t
  have hh := half_le_norm_Lent_ctr hI χ t
  have hE := Real.exp_pos (Mfun A C N t)
  have hP : 0 ≤ C * (4 * (N * (|t| + 2))) ^ A := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hh hE.le]
end PI.EF
