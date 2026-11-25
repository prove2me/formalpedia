-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_rangeSubfield_256513a2046f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:26.433743+00:00
-- url     : https://prove2.me/submissions/a590561e-b74c-4dc9-bf14-ab55b9110dd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
theorem _root_.solution {R : Type*} [CommRing R] (ρ : R →+* Ω) (hinv : ∀ r, ρ r ≠ 0 → ∃ r', ρ r' * ρ r = 1)
    (r : R) : ρ r ∈ rangeSubfield ρ hinv :=
  ⟨r, rfl⟩
end GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
