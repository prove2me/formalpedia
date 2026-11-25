-- Prove2me | solution 1 for UpperTheory.HF.Formalism.HC.HostAx.not_dvd_muW_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:20.009661+00:00
-- url     : https://prove2.me/submissions/87fcf40b-f8a7-487b-8f53-c615b9c1164a

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuNotdvdmuWofunramified
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_dvd_muW_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open UpperTheory.HF
open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem mem_pow_of_prim {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 L)) (hQ : Q.IsPrime) (hpQ : (p : 𝓞 L) ∈ Q) (η : L) (hη : IsPrimitiveRoot η p) :
    (p : 𝓞 L) ∈ Q ^ (p - 1) := by
  obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hη
  have hx : hη.toInteger - 1 ∈ Q := by
    apply hQ.mem_of_pow_mem (p - 1)
    have : (hη.toInteger - 1) ^ (p - 1) = (p : 𝓞 L) * ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Q.mul_mem_right _ hpQ
  rw [← hu]
  exact (Q ^ (p - 1)).mul_mem_right _ (Ideal.pow_mem_pow hx (p - 1))
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF.Formalism.HC.HostAx
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → p ≠ 2 → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P → (p : 𝓞 H.E) ∉ P ^ 2 → ¬ p ∣ H.muW := by
  intro φ H p hp hp2 P hP hpP hpP2 hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := (HostRaw.dvd_muW_iff _ hp.pos).1 hdvd
  have h := mem_pow_of_prim p P hP hpP ζ hζ
  have h2 : 2 ≤ p - 1 := by
    have := hp.two_le
    omega
  exact hpP2 (Ideal.pow_le_pow_right h2 h)
end UpperTheory.HF.Formalism.HC.HostAx
