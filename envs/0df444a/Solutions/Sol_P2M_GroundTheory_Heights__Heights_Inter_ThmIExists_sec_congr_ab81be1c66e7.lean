-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:08.752473+00:00
-- url     : https://prove2.me/submissions/05eae9f2-4627-46bb-9848-824f7430daa3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {P : Ideal (MRing ι)} {A B : HermLine ι} {s : MRing ι} (h : A = B)
    (hs : IsSectionOn P A s) : IsSectionOn P B s := h ▸ hs
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
