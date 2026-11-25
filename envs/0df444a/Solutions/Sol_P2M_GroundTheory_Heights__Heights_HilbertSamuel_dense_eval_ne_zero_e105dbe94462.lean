-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_dense_eval_ne_zero_e105dbe94462
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:22.033622+00:00
-- url     : https://prove2.me/submissions/a21a626a-5450-4b2e-bc4b-7a92833a2ff8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PGrowthOffHypersurfacePolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_eval_ne_zero_of_isOpen_a58e4a73048f

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨t, htV, ht⟩ := exists_eval_ne_zero_of_isOpen hQ hV hne
  exact ⟨t, htV, ht⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
