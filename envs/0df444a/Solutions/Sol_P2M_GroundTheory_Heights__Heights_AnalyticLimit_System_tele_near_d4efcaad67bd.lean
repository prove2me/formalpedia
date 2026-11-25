-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:55.728186+00:00
-- url     : https://prove2.me/submissions/589875df-4795-4102-9e29-cda9336ae86a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7
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
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : R.r x ≤ ell t) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have h1 := one_le_of_exp_le he
  have h0' : S.ell₀ ≤ ell t' := le_trans h0 (ell_anti ht' htt)
  have hC := S.C_nonneg ht h0 h1 x
  have hK := dataC_nonneg hx
  have ha : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  have he0 := errE_nonneg hC h1
  have up1 := S.near t ht h0 x hx hr
  have up2 := S.le_ph t' ht' h0' x hx
  have lo := S.mono t' t ht' htt h0 x
  have hM : S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) =
      (t ^ (1 / 3 : ℝ) + errE S.C t) + S.C * t ^ (1 / 3 : ℝ) + S.C * errE S.C t +
        S.C ^ 2 * (t ^ (1 / 3 : ℝ) + errE S.C t) + R.C * (t ^ (1 / 3 : ℝ) + errE S.C t) := by
    unfold teleConst
    rw [abs_of_nonneg hC, abs_of_nonneg hK]
    ring
  have p1 := mul_nonneg hC ha
  have p2 := mul_nonneg (sq_nonneg S.C) (add_nonneg ha he0)
  have p3 := mul_nonneg hK (add_nonneg ha he0)
  have p4 := mul_nonneg hC he0
  rw [hM, abs_le]
  constructor <;> linarith
end GroundTheory.Heights₂.Heights.AnalyticLimit.System
