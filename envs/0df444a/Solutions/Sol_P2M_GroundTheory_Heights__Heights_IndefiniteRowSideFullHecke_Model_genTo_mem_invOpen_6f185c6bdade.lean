-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:16.621686+00:00
-- url     : https://prove2.me/submissions/580703dd-5e72-4b0e-a9df-4e87e10c810c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory AlgebraicGeometry
variable (X : Scheme.{0})
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {m : ℕ} (hm : m ≠ 0) (x : genFib X) : (genTo X).base x ∈ invOpen X m := by
  have hu : IsUnit (((m : ℤ) : ℚ)) :=
    GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat m (by exact_mod_cast hm)
  have := GroundTheory.Heights₂.Heights.Model.range_baseChangeMap_subset (toSpecZ X) ℚ (m : ℤ) hu ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι] at this
  exact this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
