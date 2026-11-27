-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_hyp_inhabited_092cb4eec4d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:18.006436+00:00
-- url     : https://prove2.me/submissions/6ef73af1-b3a1-46af-8563-fa33682fca89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace RiemannExt
theorem _root_.solution :
    RiemannExt.Hyp (Polynomial ℂ) (Polynomial.X * Polynomial.X) Polynomial.X := by
  refine ⟨inferInstance, inferInstance, inferInstance, Polynomial.X_ne_zero, ?_⟩
  intro x
  refine ⟨{Polynomial.X}, 1, one_pos, ‖x Polynomial.X‖ + 1, fun y hy _ => ?_⟩
  have h1 := hy Polynomial.X (Finset.mem_singleton_self _)
  have h2 : ‖y Polynomial.X‖ ≤ ‖x Polynomial.X‖ + 1 := by
    have := norm_le_norm_add_norm_sub' (y Polynomial.X) (x Polynomial.X)
    linarith
  rw [map_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
end RiemannExt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
