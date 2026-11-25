-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_formSpace_ne_top_c7bc28259234
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:11.395568+00:00
-- url     : https://prove2.me/submissions/f61bbf87-ad39-4c29-b4d3-6f85f33d2cee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987

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
theorem _root_.solution {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} (hI : IsRelevant I) :
    formSpace I ≠ ⊤ := by
  obtain ⟨j, hj⟩ := hI
  intro htop
  have h : Pi.single j 1 ∈ formSpace I := htop ▸ Submodule.mem_top
  rw [mem_formSpace] at h
  apply hj
  have : linForm (Pi.single j (1 : ℂ)) = (X j : MvPolynomial (Fin n) ℂ) := by
    rw [← linFormMap_apply]
    simp [linFormMap, Fintype.linearCombination_apply, Pi.single_apply]
  rwa [this] at h
end GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
