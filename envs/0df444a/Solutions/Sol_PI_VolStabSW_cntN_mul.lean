-- Prove2me | solution 1 for PI.VolStabSW.cntN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:27.79248+00:00
-- url     : https://prove2.me/submissions/de4c1398-1fc3-45f9-8e36-ff5721c0d905

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]
namespace PI.VolStabSW
theorem _root_.solution (Γ : Subgroup G) (A : Set G) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    cntN Γ A (γ * g) = cntN Γ A g := by
  unfold cntN
  have e := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
    (fun γ' : Γ => A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ' : G) * g))
  rw [← e]
  congr 1
  funext γ'
  simp [mul_assoc]
end PI.VolStabSW
