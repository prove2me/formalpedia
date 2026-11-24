-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_sup_span_187dce0f4183
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:54.901803+00:00
-- url     : https://prove2.me/submissions/241984bb-092b-4108-a6ff-e4c1501f3e2c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_last_02e1f6eebe08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    graphIdeal J p ⊔ Ideal.span {X (Fin.last n)} = graphIdeal (J ⊔ Ideal.span {p}) p := by
  have hs := graphHom_surjective p
  have hmap : (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).map (graphHom p) = J ⊔ Ideal.span {p} := by
    rw [Ideal.map_sup, graphIdeal, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton,
      graphHom_X_last]
  rw [← hmap]
  show _ = Ideal.comap (graphHom p) (Ideal.map (graphHom p) _)
  rw [Ideal.comap_map_of_surjective _ hs]
  refine (sup_eq_left.mpr ?_).symm
  exact le_sup_of_le_left (Ideal.comap_mono bot_le)
end GroundTheory.Heights₂.Heights.Targets
