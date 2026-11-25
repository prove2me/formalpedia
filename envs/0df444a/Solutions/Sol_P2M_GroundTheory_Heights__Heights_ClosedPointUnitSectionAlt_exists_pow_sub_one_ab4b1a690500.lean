-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_pow_sub_one_ab4b1a690500
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:18.551704+00:00
-- url     : https://prove2.me/submissions/a82e6ecd-f54e-4ec5-885b-2216c36cf44d

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
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (P : HeightOneSpectrum (𝓞 K')) {x : K'} (hx : P.valuation K' x = 1) :
    ∃ N : ℕ, 1 ≤ N ∧ P.valuation K' (x ^ N - 1) < 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P x hx.le
  have hd : (d : 𝓞 K') ∉ P.asIdeal := d.2
  have hd1 : P.valuation K' (algebraMap (𝓞 K') K' d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr hd
  have hn : (n : 𝓞 K') ∉ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K'), ← hnd, map_mul, hx, one_mul]
    exact hd1
  have hdK : algebraMap (𝓞 K') K' d ≠ 0 := fun h => by
    rw [h, map_zero] at hd1
    exact zero_ne_one hd1
  have := P.isMaximal
  let _ : Field (𝓞 K' ⧸ P.asIdeal) := Ideal.Quotient.field _
  let _ : Fintype (𝓞 K' ⧸ P.asIdeal) := Fintype.ofFinite _
  have hq : 1 < Fintype.card (𝓞 K' ⧸ P.asIdeal) := Fintype.one_lt_card
  have hmk : ∀ a : 𝓞 K', a ∉ P.asIdeal →
      Ideal.Quotient.mk P.asIdeal a ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) = 1 := fun a ha =>
    FiniteField.pow_card_sub_one_eq_one _ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hmem : (n : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) -
      (d : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, hmk _ hn, hmk _ hd, sub_self]
  refine ⟨Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1, by omega, ?_⟩
  have e : x ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) - 1 =
      algebraMap (𝓞 K') K' ((n : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) -
        (d : 𝓞 K') ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1)) /
        algebraMap (𝓞 K') K' d ^ (Fintype.card (𝓞 K' ⧸ P.asIdeal) - 1) := by
    rw [eq_div_iff (pow_ne_zero _ hdK), map_sub, map_pow, map_pow, ← hnd]
    ring
  rw [e, map_div₀, map_pow, hd1, one_pow, div_one]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mpr hmem
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
