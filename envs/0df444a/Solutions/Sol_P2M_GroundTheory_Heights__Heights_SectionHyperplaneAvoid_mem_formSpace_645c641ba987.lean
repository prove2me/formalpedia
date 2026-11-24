-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:49.156326+00:00
-- url     : https://prove2.me/submissions/af6da62b-cfaf-4305-b41c-e3d92235fbd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b

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
theorem _root_.solution {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} :
    ℓ ∈ formSpace I ↔ linForm ℓ ∈ I := by
  simp [formSpace, linFormMap_apply]
end GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
