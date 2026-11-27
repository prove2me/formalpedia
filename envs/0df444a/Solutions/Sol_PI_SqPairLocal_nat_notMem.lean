-- Prove2me | solution 1 for PI.SqPairLocal.nat_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:40.182792+00:00
-- url     : https://prove2.me/submissions/93bc9603-36ff-4291-93e9-4bfc21600176

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c)
    (hpQ : (p : 𝓞 E) ∈ Q) : (c : 𝓞 E) ∉ Q := by
  intro hcQ
  have hcop : Nat.Coprime p c := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (c : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  have h1Q : (1 : 𝓞 E) ∈ Q := h1 ▸ Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hcQ)
  exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1Q)
end PI.SqPairLocal
