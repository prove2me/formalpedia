-- Prove2me | solution 1 for PI.SqPairLocal.glue_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:34.864806+00:00
-- url     : https://prove2.me/submissions/8b107978-1ddb-4412-8e98-de631994b0eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_ne_bot_of_max
import Theorems.Thm_PI_SqPairLocal_glue_fin

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
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (hP : PowLoc) : Glue := by
  classical
  intro hO E _ _ _ hE N L' L'' hN h' h'' p hp a
  have hp0 : (p : 𝓞 E) ≠ 0 := by
    first
      | exact_mod_cast hp.ne_zero
      | (intro h0
         have h1 := congrArg (fun t : 𝓞 E => (t : E)) h0
         simp only [map_natCast, Nat.cast_eq_zero] at h1
         exact hp.ne_zero (by exact_mod_cast h1))
  have hc : ((p : 𝓞 E) ^ a) ≠ 0 := pow_ne_zero a hp0
  have hI : Ideal.span {(p : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  obtain ⟨e, q', q'', g⟩ := glue_fin hP hO hE hN h' h'' hc
    ((Ideal.finite_factors hI).toFinset.image (fun v => v.asIdeal)) (by
      intro P hPT
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hPT
      exact v.isMaximal)
  refine ⟨e, q', q'', fun Q hQ hpQ => (g Q ?_).1⟩
  refine Finset.mem_image.mpr ⟨⟨Q, hQ.isPrime, ne_bot_of_max hQ⟩, ?_, rfl⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpQ)
end PI.SqPairLocal
