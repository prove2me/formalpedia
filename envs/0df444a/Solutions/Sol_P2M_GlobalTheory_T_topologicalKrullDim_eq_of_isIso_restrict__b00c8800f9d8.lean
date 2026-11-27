-- Prove2me | solution 1 for P2M_GlobalTheory_T_topologicalKrullDim_eq_of_isIso_restrict__b00c8800f9d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:41.134235+00:00
-- url     : https://prove2.me/submissions/2c206f37-e303-4e03-b117-346bcd6d9b7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrictStatement
import Theorems.Thm_GlobalTheory_OpenDim_topologicalKrullDim_eq_of_isIso_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (W W' : Scheme.{0}) [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W), LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens, (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  first | exact @GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict | exact GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict | (intros; apply GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict <;> assumption)
end _root_.GlobalTheory.T
