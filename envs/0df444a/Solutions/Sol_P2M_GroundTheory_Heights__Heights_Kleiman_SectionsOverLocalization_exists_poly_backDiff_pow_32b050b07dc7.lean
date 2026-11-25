-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_poly_backDiff_pow_32b050b07dc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:34.541995+00:00
-- url     : https://prove2.me/submissions/8f7ae16c-76db-4eb4-95d5-713a7ce27f6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsPolyBackDiffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution (n : ℕ) :
    ∃ P : Polynomial ℚ, ∀ t : ℚ, P.eval t - P.eval (t - 1) = t ^ n := by
  refine ⟨(1 / ((n : ℚ) + 1)) • (Polynomial.bernoulli (n + 1)).comp (Polynomial.X + 1), fun t => ?_⟩
  have h1 := Polynomial.bernoulli_eval_one_add (n + 1) (t - 1 + 1)
  simp only [Polynomial.eval_smul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, smul_eq_mul]
  rw [show (1 : ℚ) + (t - 1 + 1) = t + 1 by ring, show t - 1 + 1 = t by ring] at h1
  rw [show t - 1 + 1 = t by ring, h1]
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
