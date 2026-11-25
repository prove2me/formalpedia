-- Prove2me | solution 1 for UpperTheory.Small.not_mem_of_ramIdx_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:37.933256+00:00
-- url     : https://prove2.me/submissions/47d748a2-e206-4755-826a-2fc3096639f8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ZmodTwoQuadraticNeZero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostAx_mem_sq_of_dvd_QS
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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 H.E)) (hP : (l : 𝓞 H.E) ∈ P.asIdeal)
    (he : P.asIdeal.ramificationIdx ℤ = 1) : l ∉ H.small := by
  intro hs
  obtain ⟨P, hPp, hP0⟩ := P
  have h2 := H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hl (Nat.dvd_of_mem_primeFactors hs) P hP
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 H.E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hP
  have : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) P hb] at he'
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2
end UpperTheory.Small
