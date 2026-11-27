-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_proof_1e2c46eea6aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:35.155802+00:00
-- url     : https://prove2.me/submissions/3d309e7e-896c-49b2-825a-cf2e6e78427e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexFormsOnPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeZariskiDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_eval_eq_zero_of_mem_map_c9c7b8d71cbd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PrimeZariskiDense
theorem _root_.solution (h1 : ComplexFormsOnPoints.Statement) (h2 : PrimeComplexRadical.Statement)
    (h3 : ComplexMinimalPrimesContract.Statement) : PrimeZariskiDense.Statement := by
  intro K _ ι _ P j hP hj g hg z hz
  by_cases hrel : IsRelevant P
  · set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc
    have hgj : g * map (Int.castRingHom ℂ) j ∈ Pc := by
      refine h1 K ι P hP hrel _ fun w hw => ?_
      rw [map_mul]
      by_cases hjw : eval w (map (Int.castRingHom ℂ) j) = 0
      · rw [hjw, mul_zero]
      · rw [hg w hw hjw, zero_mul]
    have hrad : Pc.radical = Pc := (h2 (Σ k, ι k) P hP).radical
    have hgPc : g ∈ Pc := by
      rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro Q hQ
      change Q ∈ Pc.minimalPrimes at hQ
      have hQp : Q.IsPrime := hQ.1.1
      have hjQ : map (Int.castRingHom ℂ) j ∉ Q := by
        intro h
        apply hj
        rw [← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
        exact h
      exact (hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ
    exact PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc
  · exfalso
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    obtain ⟨i, hi⟩ := hz.1 k
    apply hi
    simpa using hz.2 _ (hk i)
end PrimeZariskiDense
end GroundTheory.Heights₂.Heights.HilbertSamuel
