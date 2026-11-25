-- Prove2me | solution 1 for PI.CompDegEF.intValuation_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:58.464947+00:00
-- url     : https://prove2.me/submissions/16d6fe9c-f886-4037-8251-938334ce98b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ placesOver E l) :
    v.intValuation ((l : ℕ) : 𝓞 E) = WithZero.exp (-(v.asIdeal.ramificationIdx ℤ : ℤ)) := by
  classical
  have hl0 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  rw [v.intValuation_if_neg hl0]
  suffices h : (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {((l : ℕ) : 𝓞 E)})).factors =
      v.asIdeal.ramificationIdx ℤ by rw [h]
  have hle : Ideal.span {((l : ℕ) : ℤ)} ≤ v.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hv
  have hunder : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.under ℤ :=
    (Int.ideal_span_isMaximal_of_prime l).eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle
  haveI : v.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := ⟨hunder⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((l : ℕ) : ℤ)}) =
      Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((l : ℕ) : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count _ _ hne, hmap,
    Ideal.count_associates_factors_eq (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
      v.isPrime v.ne_bot,
    UniqueFactorizationMonoid.factors_eq_normalizedFactors]
end PI.CompDegEF
