-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:32.912204+00:00
-- url     : https://prove2.me/submissions/9de2fe58-a3e0-4b77-a78a-93ea25205b59

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = -WithZero.log (v.valuation K x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  dsimp only at hx ⊢
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hx
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  rw [FractionalIdeal.count_well_defined K v (a := (s : 𝓞 K)) (J := Ideal.span {r})
    (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]) ?_]
  · rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hr,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hs, ← WithZero.exp_sub, WithZero.log_exp]
    ring
  · rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
end ReciprocityTheory.Neutral.Bridge.HCFR
