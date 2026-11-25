-- Prove2me | solution 1 for PI.KerIso.DetOrdW.val_natCast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:21.469084+00:00
-- url     : https://prove2.me/submissions/761e4ce1-6680-44b9-9416-01a59f5a8898

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne

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
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) :
    𝔭.valuation K (s : K) = 1 := by
  have hcast : ((s : ℕ) : K) = algebraMap (𝓞 K) K (s : 𝓞 K) := by simp
  rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hs𝔭
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
  have h1 : (1 : 𝓞 K) ∈ 𝔭.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at e
    rw [← e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hs𝔭) (Ideal.mul_mem_left _ _ hp)
  exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
end PI.KerIso.DetOrdW
