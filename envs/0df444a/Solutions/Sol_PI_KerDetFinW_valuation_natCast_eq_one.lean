-- Prove2me | solution 1 for PI.KerDetFinW.valuation_natCast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:26.542935+00:00
-- url     : https://prove2.me/submissions/dd50f1af-151c-432b-845d-c6306fad7961

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) :
    𝔭.valuation K (U : K) = 1 := by
  have hU' : ((U : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hU
    apply 𝔭.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : ((a * (U : ℤ) + b * (p : ℤ) : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp𝔭)
    rw [hab, Int.cast_one] at h2
    exact h2
  have hK : ((U : ℕ) : K) = algebraMap (𝓞 K) K (U : 𝓞 K) := (map_natCast _ _).symm
  rw [hK, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  refine le_antisymm (𝔭.intValuation_le_one _) (not_lt.mp fun hlt => hU' ?_)
  exact Ideal.dvd_span_singleton.mp ((𝔭.intValuation_lt_one_iff_dvd _).mp hlt)
end PI.KerDetFinW
