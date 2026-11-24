-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_sum_a71ef09db231
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:18.191191+00:00
-- url     : https://prove2.me/submissions/2f2f1032-3151-43e4-b41a-6e0ef3b5f562

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartDetRatio
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a a' : Fin 2 → Ω) :
    T.detE e (∑ q, a q • b q) (∑ q, a' q • b q) = (a 0 * a' 1 - a 1 * a' 0) * T.detE e (b 0) (b 1) := by
  simp only [T.detE, Fin.sum_univ_two, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring
end ChartDetRatio
end GroundTheory.Heights₂.Heights.Inter
