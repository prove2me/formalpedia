-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_prime_mem_unique_e91ad699f71a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:02.982427+00:00
-- url     : https://prove2.me/submissions/df8206bf-6d7e-4f56-ab0e-757ea162fe2e

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions.Examples₂.PlacesToy
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]
namespace Formalism.BasicNotions.Examples₂.PlacesToy
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpw : (p : 𝓞 K) ∈ w.asIdeal) (hqw : (q : 𝓞 K) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : ((a : 𝓞 K) * (p : 𝓞 K) + (b : 𝓞 K) * (q : 𝓞 K)) ∈ w.asIdeal :=
    w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hpw) (w.asIdeal.mul_mem_left _ hqw)
  have h2 : ((a : 𝓞 K) * (p : 𝓞 K) + (b : 𝓞 K) * (q : 𝓞 K)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at this
    exact this
  rw [h2] at h1
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
end Formalism.BasicNotions.Examples₂.PlacesToy
