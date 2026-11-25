-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientLemmas.torsion_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:01.538541+00:00
-- url     : https://prove2.me/submissions/d03ae8b0-2d55-43d3-8ac9-d7161bb2c0e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientLemmas
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientLemmas
theorem _root_.solution {r : ℕ} (X : Data E r) (ξ : Fin r → E) :
    Submodule.torsion (𝓞 E) (Mp X ξ ⧸ Nx X ξ) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨⟨a, ha⟩, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have haq' : (a : 𝓞 E) • (Submodule.Quotient.mk m : Mp X ξ ⧸ Nx X ξ) = 0 := haq
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at haq'
  obtain ⟨e, he⟩ := haq'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have ha0 : (a : E) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero ha)
  rw [Submodule.coe_smul, smul_O] at he
  show ∃ e : E, (m : Fin r → E) = e • ξ
  refine ⟨e / a, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← he, smul_smul, inv_mul_cancel₀ ha0, one_smul]
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientLemmas
