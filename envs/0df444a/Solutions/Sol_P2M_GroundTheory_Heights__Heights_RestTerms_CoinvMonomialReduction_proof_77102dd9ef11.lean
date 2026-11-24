-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvMonomialReduction_proof_77102dd9ef11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:28.171423+00:00
-- url     : https://prove2.me/submissions/1a0a43a9-5e3f-40b2-95f9-acdaff592928

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvMonomialReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Coinv
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvMonomialReduction
theorem _root_.solution (h1 : CoinvStepReduction.Statement) :
    CoinvMonomialReduction.Statement := by
  intro K _ _ f n e
  classical
  let r : Fin f × Fin n → Fin f × Fin n → Prop := fun u v => toLex u < toLex v
  have : IsStrictTotalOrder (Fin f × Fin n) r :=
    inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))
  have wf : WellFounded
      (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFounded_of_finite r wellFounded_lt
  induction e using wf.induction with
  | _ e ih =>
  by_cases hu : IsUnderStaircase e
  · exact ⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩
  · simp only [IsUnderStaircase, not_forall, not_le] at hu
    obtain ⟨⟨b, k⟩, hbk⟩ := hu
    obtain ⟨T, c, hT, hmem⟩ := h1 K f n b k e (by simpa using hbk)
    have hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e := by
      intro e' he'
      refine Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩
      exact Prod.Lex.toLex_lt_toLex.mp hj
    choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')
    refine ⟨∑ e' ∈ T, c e' • w e',
      Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩
    have hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' =
        (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) +
          ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e') := by
      simp only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))
end CoinvMonomialReduction
end GroundTheory.Heights₂.Heights.RestTerms
