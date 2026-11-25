-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaFirstCoordSplit_term_le_3db75cf9db45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:20.268708+00:00
-- url     : https://prove2.me/submissions/aa5eed99-023b-40ad-bd50-13fc44696f4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaFirstCoordSplit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_sq_coord_le_d1ab1fa771ab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Real
open GroundTheory.Heights₂.Heights.KThetaFirstCoordSplit
namespace GroundTheory.Heights₂.Heights.KThetaFirstCoordSplit
theorem _root_.solution {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by
  set v := intVec k + (a + u₁) with hv
  have hassoc : intVec k + a + u₁ = v := add_assoc _ _ _
  rw [hassoc]
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  have hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0) := by simp [hv, intVec]
  have hδle : δ ≤ |v 0| := by
    have h := Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0)
      (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))
    refine h.trans (le_of_eq ?_)
    rw [Real.dist_eq, hv0]
    congr 1
    push_cast
    ring
  have hδsq : δ ^ 2 ≤ v 0 ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ hδ0 hδle 2
  have hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v := by
    have := KCoord.sq_coord_le Y hY 0 v
    rwa [hρY] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v := by
    rw [div_le_iff₀ hρ2]
    linarith [mul_comm (ρ ^ 2) (qf Y v)]
  have hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := by
    apply exp_le_exp.2
    have h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2) := by
      field_simp
    have h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hexp (exp_pos _).le
end GroundTheory.Heights₂.Heights.KThetaFirstCoordSplit
