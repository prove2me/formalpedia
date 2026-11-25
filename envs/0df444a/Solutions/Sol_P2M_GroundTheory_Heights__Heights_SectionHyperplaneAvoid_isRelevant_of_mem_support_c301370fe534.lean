-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_isRelevant_of_mem_support_c301370fe534
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:13.135797+00:00
-- url     : https://prove2.me/submissions/47b0b05f-5e06-4cc2-9568-f4b509e30c72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
namespace GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : W ∈ (divCycle J u).support) : IsRelevant W := by
  rw [Finsupp.mem_support_iff] at hW
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply] at hW
  by_contra h
  exact hW (if_neg fun h' => h h'.2)
end GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
