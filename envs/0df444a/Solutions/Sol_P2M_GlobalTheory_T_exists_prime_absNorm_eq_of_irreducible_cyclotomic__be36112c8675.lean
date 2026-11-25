-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_prime_absNorm_eq_of_irreducible_cyclotomic__be36112c8675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:56.339137+00:00
-- url     : https://prove2.me/submissions/238d65f2-530c-4387-9714-0b3b592f2be8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement
import Theorems.Thm_GlobalTheory_CyclotomicPrimes_exists_prime_absNorm_eq_of_irreducible_cyclotomic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by
  first | exact @GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic | exact GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic | (intros; apply GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic <;> assumption)
end _root_.GlobalTheory.T
