-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_finite_centres_5a68fbf492f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:22.629141+00:00
-- url     : https://prove2.me/submissions/3d04c4c0-e03f-4dfc-a6a8-517fbceb6921

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T] [NumberField K']
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution [NumberField K'] (m : Ideal (curveRing y)) (hm : m.IsMaximal) :
    {P : HeightOneSpectrum (𝓞 K') |
      ∃ q : ℕ, q.Prime ∧ (q : curveRing y) ∈ m ∧ (q : 𝓞 K') ∈ P.asIdeal}.Finite := by
  by_cases h : ∃ q0 : ℕ, q0.Prime ∧ (q0 : curveRing y) ∈ m
  · obtain ⟨q0, hq0, hq0m⟩ := h
    have hne : Ideal.span {(q0 : 𝓞 K')} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq0.ne_zero
    refine (Ideal.finite_factors hne).subset ?_
    rintro P ⟨q, hq, hqm, hqP⟩
    have hqq : q = q0 := by
      by_contra hne'
      obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (q0 : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hq0).mpr hne')
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (a : curveRing y) * q + (b : curveRing y) * q0 = 1 := by
        have := congrArg (Int.cast : ℤ → curveRing y) hab
        push_cast at this
        exact this
      rw [← e]
      exact m.add_mem (m.mul_mem_left _ hqm) (m.mul_mem_left _ hq0m)
    subst hqq
    exact Ideal.dvd_span_singleton.mpr hqP
  · refine Set.finite_empty.subset ?_
    rintro P ⟨q, hq, hqm, -⟩
    exact h ⟨q, hq, hqm⟩
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
