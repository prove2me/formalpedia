-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_restPolynomial_323c14e620df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:35.071353+00:00
-- url     : https://prove2.me/submissions/85519e69-80b6-48de-a1e1-6c256aaf814f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_filter_pair_8f784f72c70f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (s : Finset (Fin (r + a)))
    (α β : Fin f → ℚ)
    (hy : ∀ σ i, (if (yIndex f r a c σ i).1 = τ ∧ (yIndex f r a c σ i).2 ∈ s then 1 else 0 : ℕ) =
      (α σ : ℚ))
    (hz : ∀ σ i, (if (zIndex f r a c σ i).1 = τ ∧ (zIndex f r a c σ i).2 ∈ s then 1 else 0 : ℕ) =
      (β σ : ℚ)) :
    ∑ i ∈ s, pderiv (τ, i) (restPolynomial f r a c) =
      C (((f * (r * a) + 1 : ℕ) : ℚ) * (c.sign * r * ∑ σ, α σ)) *
        (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) := by
  classical
  rw [← sumPderiv_apply s (fun i => ((τ, i) : Fin f × Fin (r + a)))]
  refine (derivation_restPolynomial f r a c _ α β (fun σ i => ?_) (fun σ i => ?_)).2
  · rw [sumPderiv_X, card_filter_pair, ← hy σ i]
  · rw [sumPderiv_X, card_filter_pair, ← hz σ i]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
