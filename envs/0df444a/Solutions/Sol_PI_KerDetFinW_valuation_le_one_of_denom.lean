-- Prove2me | solution 1 for PI.KerDetFinW.valuation_le_one_of_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:59.04177+00:00
-- url     : https://prove2.me/submissions/385df326-62a1-46cf-9204-daf84fd9e60e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Theorems.Thm_PI_KerDetFinW_valuation_natCast_eq_one

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
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) {x : K}
    (hx : (U : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h1 : 𝔭.valuation K (U : K) = 1 := valuation_natCast_eq_one 𝔭 hp𝔭 hU
  have h2 : 𝔭.valuation K ((U : K) * x) ≤ 1 := by
    rw [← hr, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact 𝔭.intValuation_le_one r
  rwa [map_mul, h1, one_mul] at h2
end PI.KerDetFinW
