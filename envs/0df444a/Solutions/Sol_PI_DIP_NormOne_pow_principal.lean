-- Prove2me | solution 1 for PI.DIP.NormOne.pow_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:03.102186+00:00
-- url     : https://prove2.me/submissions/cd17bd6c-33b5-43db-89e2-006fb342ba11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace PI.DIP.NormOne
theorem _root_.solution {𝔞 𝔟 : Submodule (𝓞 E) E} (hab : 𝔞 * 𝔟 = 1) :
    ∃ (h : ℕ) (a : E), 0 < h ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {a} := by
  have hba : 𝔟 * 𝔞 = 1 := by rw [mul_comm]; exact hab
  have hfa : IsFractional (𝓞 E)⁰ 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨Units.mkOfMulEqOne 𝔞 𝔟 hab, rfl⟩)
  have hfb : IsFractional (𝓞 E)⁰ 𝔟 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨Units.mkOfMulEqOne 𝔟 𝔞 hba, rfl⟩)
  let A : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔞, hfa⟩
  let B : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔟, hfb⟩
  have hAB : A * B = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((A * B : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) =
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact hab
  let u : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mkOfMulEqOne A B hAB
  let g := ClassGroup.mk E u
  have h1 : ClassGroup.mk E (u ^ orderOf g) = 1 := by
    rw [map_pow]
    exact pow_orderOf_eq_one g
  have hP := (ClassGroup.mk_eq_one_iff).1 h1
  obtain ⟨⟨a, ha⟩⟩ := hP
  refine ⟨orderOf g, a, orderOf_pos g, ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl
end PI.DIP.NormOne
