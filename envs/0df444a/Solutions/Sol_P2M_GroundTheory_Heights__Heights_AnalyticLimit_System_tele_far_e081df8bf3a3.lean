-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:52:11.342215+00:00
-- url     : https://prove2.me/submissions/bd142144-feae-4c82-85b5-d32c61473dd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_le_978993fb0664
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_C_nonneg_072e5126db6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_dataC_nonneg_8791ea7e7f4c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section
open GroundTheory.Heights₂.Heights.AnalyticLimit.System
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
  (S : System R)
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.System
theorem _root_.solution {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : ell t < R.r x) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * Real.log (R.r x) := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have h1 := one_le_of_exp_le he
  have h0' : S.ell₀ ≤ ell t' := le_trans h0 (ell_anti ht' htt)
  have hC := S.C_nonneg ht h0 h1 x
  have hK := dataC_nonneg hx
  have hL : 1 ≤ Real.log (R.r x) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have up1 := S.ph_le t ht h0 x
  have up2 := S.le_ph t' ht' h0' x hx
  have up3 := R.le_φ x hx
  have lo := S.mono t' t ht' htt h0 x
  have hCe : S.C * errE S.C t ≤ S.C * S.C := mul_le_mul_of_nonneg_left (errE_le hC h1) hC
  have hM : S.teleConst * Real.log (R.r x) = Real.log (R.r x) + S.C * Real.log (R.r x) +
      S.C ^ 2 * Real.log (R.r x) + R.C * Real.log (R.r x) := by
    unfold teleConst
    rw [abs_of_nonneg hC, abs_of_nonneg hK]
    ring
  have q1 : S.C ≤ S.C * Real.log (R.r x) := le_mul_of_one_le_right hC hL
  have q2 : S.C ^ 2 ≤ S.C ^ 2 * Real.log (R.r x) := le_mul_of_one_le_right (sq_nonneg _) hL
  have q3 : S.C * S.C = S.C ^ 2 := (sq S.C).symm
  rw [hM, abs_le]
  constructor <;> nlinarith
end GroundTheory.Heights₂.Heights.AnalyticLimit.System
