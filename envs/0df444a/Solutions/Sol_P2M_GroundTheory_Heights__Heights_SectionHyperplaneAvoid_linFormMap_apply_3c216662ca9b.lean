-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_linFormMap_apply_3c216662ca9b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:12.769716+00:00
-- url     : https://prove2.me/submissions/294a0431-6e35-425b-b7ae-a8c739ce4aab

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
theorem _root_.solution {n : ℕ} (ℓ : Fin n → ℂ) : linFormMap n ℓ = linForm ℓ := by
  simp [linFormMap, linForm, Fintype.linearCombination_apply, C_mul']
end GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
