-- Prove2me | solution 1 for PI.KerIso.DetOrdW.val_le_one_of_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:54.942192+00:00
-- url     : https://prove2.me/submissions/6c89736e-46f8-4888-9948-0f73dbff591c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
import Theorems.Thm_PI_KerIso_DetOrdW_val_natCast_eq_one

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
open PI PI.KerIso PI.KerIso.DetOrdW
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace PI.KerIso.DetOrdW
theorem _root_.solution (𝔭 : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) {x : K}
    (hx : (s : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h : 𝔭.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := 𝔭.valuation_le_one (K := K) r
  rw [hr, map_mul, val_natCast_eq_one 𝔭 hp hs, one_mul] at h
  exact h
end PI.KerIso.DetOrdW
