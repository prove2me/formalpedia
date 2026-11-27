-- Prove2me | solution 1 for UpperTheory.Small.card_quot_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:42:10.732696+00:00
-- url     : https://prove2.me/submissions/d3e51507-9c46-42a5-9c46-3d7927b2c26f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ZmodTwoQuadraticNeZero
import Theorems.Thm_UpperTheory_Small_zmod_two_quadratic_ne_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Small
theorem _root_.solution (P : HeightOneSpectrum (𝓞 H.E)) : Nat.card (𝓞 H.E ⧸ P.asIdeal) ≠ 2 := by
  intro hc
  have h8 := H.hyp.2.2.1
  obtain ⟨k, hk⟩ : ∃ k, H.q = 8 * k + 3 := ⟨H.q / 8, by omega⟩
  have hx : ((1 + H.sqq) / 2) ^ 2 - (1 + H.sqq) / 2 + ((2 * k + 1 : ℕ) : H.E) = 0 := by
    have h := H.sqq_sq
    rw [hk] at h
    push_cast at h ⊢
    linear_combination (1 / 4 : H.E) * h
  have hi : IsIntegral ℤ ((1 + H.sqq) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 1 : ℕ) : ℤ), by monicity!, ?_⟩
    simpa using hx
  let z : 𝓞 H.E := ⟨_, hi⟩
  have hz : z ^ 2 - z + ((2 * k + 1 : ℕ) : 𝓞 H.E) = 0 := by
    apply RingOfIntegers.ext
    simp only [map_add, map_sub, map_pow, map_natCast, map_zero]
    exact hx
  haveI := P.isPrime
  haveI : Finite (𝓞 H.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (𝓞 H.E ⧸ P.asIdeal)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := ZMod.ringEquivOfPrime (𝓞 H.E ⧸ P.asIdeal) Nat.prime_two (Nat.card_eq_fintype_card.symm.trans hc)
  have h := congrArg (fun t => e.symm (Ideal.Quotient.mk P.asIdeal t)) hz
  simp only [map_add, map_sub, map_pow, map_natCast, map_zero] at h
  generalize e.symm (Ideal.Quotient.mk P.asIdeal z) = u at h
  push_cast at h
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, zero_add] at h
  exact zmod_two_quadratic_ne_zero u h
end UpperTheory.Small
