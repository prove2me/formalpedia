-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:45.06532+00:00
-- url     : https://prove2.me/submissions/e2c71a53-16b7-4b98-82e2-cc9737e2cad9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lsq_scl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_rhoSq_scl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_bco_scl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    de (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * de x i := by
  have h := de_sq (tailPt (sclPt a0 r x)) i.succ
  rw [lsq_scl a0 r hr, rhoSq_scl a0 r hr, bco_scl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r)] at h
  have h2 := de_sq x i
  have : de (tailPt (sclPt a0 r x)) i.succ ^ 2 = (r ^ 2 * de x i) ^ 2 := by rw [h, mul_pow (r ^ 2) (de x i), h2]; ring
  have p1 := de_nonneg (tailPt (sclPt a0 r x)) i.succ
  have p2 := de_nonneg x i
  exact (pow_left_inj₀ p1 (by positivity) two_ne_zero).1 this
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
