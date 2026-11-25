-- Prove2me | solution 1 for UpperTheory.Mu.exists_unit_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:08.530068+00:00
-- url     : https://prove2.me/submissions/f0accb37-96b6-43d8-8dd9-78906e56730d

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_ResidueEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Mu
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace UpperTheory.Mu
theorem _root_.solution {z : L} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∃ ζ : (𝓞 L)ˣ, ((ζ : 𝓞 L) : L) = z := by
  obtain ⟨m, hm, hzm⟩ := hz
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow hm ?_
    rw [hzm]
    exact isIntegral_one
  let y : 𝓞 L := ⟨z, hint⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    push_cast
    exact hzm
  exact ⟨(IsUnit.of_pow_eq_one hy hm.ne').unit, rfl⟩
end UpperTheory.Mu
