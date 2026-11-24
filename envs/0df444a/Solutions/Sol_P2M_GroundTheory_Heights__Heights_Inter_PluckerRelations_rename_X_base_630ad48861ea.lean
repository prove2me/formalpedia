-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_rename_X_base_630ad48861ea
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:08.34655+00:00
-- url     : https://prove2.me/submissions/3e9271f6-0f8a-473a-8ca2-bd741c13c2e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerRelations
theorem _root_.solution (j : S.ι) :
    (rename (T.yyEmb 0) (X ⟨T.YBlk.base, j⟩ : MRing S.YIdx) : MRing S.WIdx) = X ⟨T.WBlk.base, j⟩ :=
  rename_X _ _
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
