-- Prove2me | solution 1 for PI.GaugeCharW.extChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:53.880783+00:00
-- url     : https://prove2.me/submissions/f5c39b14-2279-4ead-b46d-fee2e41b510e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IntInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GaugeCharW
namespace PI.GaugeCharW
theorem _root_.solution : ExtChar := by
  intro G _ _ _ K U hU g hg hKU
  let j : K →+ G ⧸ U := (QuotientAddGroup.mk' U).comp K.subtype
  have hker : ∀ k ∈ j.ker, g.comp K.subtype k = 0 := by
    intro k hk
    have hkU : (k : G) ∈ U := (QuotientAddGroup.eq_zero_iff _).mp hk
    exact hKU k k.2 hkU
  let g' : K ⧸ j.ker →+ AddCircle (1 : ℝ) := QuotientAddGroup.lift j.ker (g.comp K.subtype) hker
  obtain ⟨η', hη'⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g'
  let η : G →+ AddCircle (1 : ℝ) := η'.comp (QuotientAddGroup.mk' U)
  have hηU : ∀ x ∈ U, η x = 0 := fun x hx => by
    show η' (QuotientAddGroup.mk' U x) = 0
    rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff x).mpr hx, map_zero]
  refine ⟨g - η, ?_, ?_, ?_⟩
  · refine continuous_of_continuousAt_zero (g - η) ?_
    have hmem : (U : Set G) ∈ nhds (0 : G) := hU.mem_nhds U.zero_mem
    refine hg.continuousAt.congr ?_
    filter_upwards [hmem] with u hu
    rw [AddMonoidHom.sub_apply, hηU u hu, sub_zero]
  · intro x hx
    have h1 : η x = g' (QuotientAddGroup.mk (⟨x, hx⟩ : K)) := by
      rw [← hη']; rfl
    rw [AddMonoidHom.sub_apply, h1]
    show g x - (g.comp K.subtype) ⟨x, hx⟩ = 0
    exact sub_self _
  · intro x hx
    rw [AddMonoidHom.sub_apply, hηU x hx, sub_zero]
end PI.GaugeCharW
