-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_proof_21ce6d6c2573
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:36.882027+00:00
-- url     : https://prove2.me/submissions/21330686-7fed-49a4-8378-1ea611fb7078

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_comp_toPoly_dea409fd7470
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_algebraMap_2078138e67d2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open ChartDomain
namespace GroundTheory.Heights₂.Heights.Vertical
namespace ChartDomain
theorem _root_.solution : ChartDomain.Statement := by
  intro D _ _ n e Q j hQ hQD hXj
  have hxj : Ideal.Quotient.mk Q (X j) ≠ 0 := fun h => hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (MvPolynomial (Fin n) D ⧸ Q) := Ideal.Quotient.isDomain Q
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hxj
  have : IsDomain (Base Q j) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (toPoly Q j e) :=
    Function.LeftInverse.injective (g := fromPoly Q j e) fun x => RingHom.congr_fun (fromPoly_comp_toPoly Q j) x
  refine ⟨Function.Injective.isDomain _ hinj, ?_⟩
  intro a b hab
  have h := congrArg (toPoly Q j e) hab
  rw [toPoly_algebraMap, toPoly_algebraMap] at h
  have h2 := IsLocalization.injective (Base Q j) hle (C_injective _ _ h)
  have h3 : C (a - b) ∈ Q := by rw [map_sub]; exact Ideal.Quotient.eq.mp h2
  exact sub_eq_zero.mp (hQD _ h3)
end ChartDomain
end GroundTheory.Heights₂.Heights.Vertical
