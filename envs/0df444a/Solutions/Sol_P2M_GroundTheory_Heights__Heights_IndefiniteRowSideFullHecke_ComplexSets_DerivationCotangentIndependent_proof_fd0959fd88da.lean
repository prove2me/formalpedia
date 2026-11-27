-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_DerivationCotangentIndependent_proof_fd0959fd88da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:22.747988+00:00
-- url     : https://prove2.me/submissions/b8bb4307-acbc-4533-b274-f5cb9524a596

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDerivationCotangentIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_derivation_det_not_mem_28a934ea20c0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace DerivationCotangentIndependent
theorem _root_.solution : DerivationCotangentIndependent.Statement := by
  intro T _ P _ h D f hf hdet a hsum i

  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl (Finset.univ : Finset (Fin h)) a
  choose b hb using fun k => hs k (Finset.mem_univ k)

  have hmax : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap T (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hsq : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) ∈ (P ^ 2).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_pow, ← hmax]
    have : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) =
        algebraMap T (Localization.AtPrime P) (s : T) * ∑ k, a k * algebraMap T (Localization.AtPrime P) (f k) := by
      simp only [map_sum, map_mul, Finset.mul_sum, hb, Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hsum
  obtain ⟨⟨⟨y, hy⟩, u⟩, hyu⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 hsq
  rw [← map_mul] at hyu
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 hyu
  have hbi : b i ∈ P := by
    refine mem_of_derivation_det_not_mem P D f hf hdet b ((c : T) * (u : T)) ?_ ?_ i
    · exact (P.primeCompl.mul_mem c.2 u.2 : _)
    · have : (c : T) * (u : T) * ∑ k, b k * f k = (c : T) * y := by rw [← hc]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hy

  have hsa : algebraMap T (Localization.AtPrime P) (s : T) * a i ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [← Algebra.smul_def, ← hb i]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hbi
  have hs' : algebraMap T (Localization.AtPrime P) (s : T) ∉ maximalIdeal (Localization.AtPrime P) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]; exact s.2
  exact ((maximalIdeal.isMaximal (Localization.AtPrime P)).isPrime.mem_or_mem hsa).resolve_left hs'
end DerivationCotangentIndependent
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
