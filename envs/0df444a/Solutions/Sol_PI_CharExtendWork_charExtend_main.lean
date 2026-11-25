-- Prove2me | solution 1 for PI.CharExtendWork.charExtend_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:53.829709+00:00
-- url     : https://prove2.me/submissions/fa6bcc88-ce70-4498-96e8-d61883f65529

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterExtension_UnitsComplexExistsZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CharExtendWork
namespace PI.CharExtendWork
theorem _root_.solution : PI.CharExtend := by
  intro G _ H χ
  letI : DivisibleBy (Additive ℂˣ) ℤ := divisibleUnitsComplex
  have hB : Module.Baer ℤ (Additive ℂˣ) := Module.Baer.of_divisible (Additive ℂˣ)
  let f : Additive H →+ Additive G := MonoidHom.toAdditive H.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.val_injective hxy
  obtain ⟨h, hh⟩ := hB.extension_property_addMonoidHom f hf (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this
end PI.CharExtendWork
