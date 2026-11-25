-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_fderiv_logh_bsmul_524bae19d6b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:22.839802+00:00
-- url     : https://prove2.me/submissions/2eedfe5e-e0c0-48ad-8769-4fae0171d2e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
theorem _root_.solution (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d z) =
      deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  have hφ : HasFDerivAt φ (fderiv ℝ φ z) z :=
    ((logh_contDiffAt hA hz).differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => z + s • bsmul d z) (bsmul d z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bsmul d z)).const_add z
  have h1 : HasDerivAt (fun s : ℝ => φ (z + s • bsmul d z)) (fderiv ℝ φ z (bsmul d z)) 0 := by
    exact hφ.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, ∀ k, 1 + (s : ℂ) * d k ≠ 0 :=
    eventually_all.mpr fun k => ContinuousAt.eventually_ne (by fun_prop) (by simp)
  have heq : (fun s : ℝ => φ (z + s • bsmul d z)) =ᶠ[𝓝 0]
      fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k) + φ z := by
    filter_upwards [hne] with s hs
    have hp : z + s • bsmul d z = fun p => (1 + (s : ℂ) * d p.1) * z p := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, bsmul, Complex.real_smul]
      ring
    have hpos : 0 < ∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hs k)) _
    simp only [φ]
    rw [hp, A.smul (fun k => 1 + (s : ℂ) * d k) z hs, Real.log_mul hpos.ne' (A.pos z hz).ne']
  rw [(h1.congr_of_eventuallyEq heq.symm).deriv.symm, deriv_add_const]
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
