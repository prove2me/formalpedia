-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.int_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:18.999073+00:00
-- url     : https://prove2.me/submissions/a8dd9452-a1ef-4452-ab0f-8531a8303cdd

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_vol_smul
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SplitFlip_nabs_of_valuation_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (u : kˣ) (hu : valuation k (u : k) = 1) (f : k → ℂ) : ∫ x, f (u * x) ∂m = ∫ x, f x ∂m := by
  let e : k ≃ᵐ k := (Homeomorph.mulLeft₀ (u : k) u.ne_zero).toMeasurableEquiv
  have hp : MeasurePreserving e m m := by
    refine ⟨e.measurable, Measure.ext fun s hs => ?_⟩
    rw [MeasurableEquiv.map_apply]
    have : e ⁻¹' s = u⁻¹ • s := by
      ext x; rw [Set.mem_inv_smul_set_iff]; rfl
    rw [this, vol_smul hm, nabs_of_valuation_eq_one (by simp [hu])]
    simp
  exact hp.integral_comp' f
end PositivityTheory.ThKG.Std
