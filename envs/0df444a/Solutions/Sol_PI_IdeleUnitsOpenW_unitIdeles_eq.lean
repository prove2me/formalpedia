-- Prove2me | solution 1 for PI.IdeleUnitsOpenW.unitIdeles_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:19.784805+00:00
-- url     : https://prove2.me/submissions/8fcf2d19-538c-4e9b-9764-900d38dd8f51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.IdeleUnitsOpenW
variable (L : Type) [Field L] [NumberField L]
namespace PI.IdeleUnitsOpenW
theorem _root_.solution :
    (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L)) =
      (fun u : Ideles L => (u : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L ∩
        (fun u : Ideles L => ((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L := by
  ext u
  constructor
  · intro hu
    have hu' : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1 := hu
    refine ⟨fun v => (hu' v).le, fun v => ?_⟩
    have e := congrArg Valued.v (comp_mul_inv L u v)
    rw [map_mul, hu' v, one_mul, map_one] at e
    exact e.le
  · rintro ⟨h1, h2⟩
    show ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1
    intro v
    have e := congrArg Valued.v (comp_mul_inv L u v)
    rw [map_mul, map_one] at e
    have hle1 : Valued.v ((u : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h1 v
    have hle2 : Valued.v (((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h2 v
    refine le_antisymm hle1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
      _ ≤ Valued.v ((u : AdeleRing (𝓞 L) L).2 v) * 1 := by gcongr
      _ = _ := mul_one _
end PI.IdeleUnitsOpenW
