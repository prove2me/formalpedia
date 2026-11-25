-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetLift_differentiableAt_lift_4f284a106fc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:13.202518+00:00
-- url     : https://prove2.me/submissions/4a69bca0-d63d-472c-b17a-f9806f1d704f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)
open GroundTheory.Heights₂.Heights.SheetLift
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SheetLift
theorem _root_.solution [DecidableEq K] {e : ℕ} (i0 : (k : K) → ι k) (k0 : K)
    {h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (hd : DifferentiableAt ℂ h y)
    (hne : h y i0 ≠ 0) : DifferentiableAt ℂ (fun y' => lift i0 k0 (h y')) y := by
  have hc : ∀ i, DifferentiableAt ℂ (fun y' => h y' i) y := fun i => differentiableAt_pi.mp hd i
  refine differentiableAt_pi.mpr fun p => ?_
  simp only [lift, div_eq_mul_inv]
  refine DifferentiableAt.mul ?_ ((hc (Function.update i0 p.1 p.2)).mul ((hc i0).inv hne))
  by_cases hp : p.1 = k0
  · simp only [hp, if_true]
    exact hc i0
  · simp only [hp, if_false]
    exact differentiableAt_const _
end GroundTheory.Heights₂.Heights.SheetLift
