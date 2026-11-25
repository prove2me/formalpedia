-- Prove2me | solution 1 for P2M_GlobalTheory_QFam_map_E__div_period_bb6678e0fe03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:15.40192+00:00
-- url     : https://prove2.me/submissions/5326c997-dab0-4219-9f35-99c11e2cde91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapEisensteinDivPeriod
import Theorems.Thm_P2M_GlobalTheory_QFam_E__div_period_eq_e177b375d23b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) :
    g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6)
      = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 := by
  rw [E₆_div_period_eq h₀, E₆_div_period_eq h₁, map_neg, map_mul, h, map_ofNat]
end GlobalTheory.QFam
