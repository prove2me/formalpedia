-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_Normality_hyp_inhabited_c6aa3589c903
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:05:43.737644+00:00
-- url     : https://prove2.me/submissions/7cce2a26-0543-48d5-82d8-4e31a4993900

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
namespace Normality
theorem _root_.solution :
    Normality.Hyp (Polynomial ℤ) 1 Polynomial.X 1 := by
  have hft : @Algebra.FiniteType ℤ (Polynomial ℤ) _ _ Polynomial.algebraOfAlgebra := inferInstance
  refine ⟨by convert hft <;> rfl, inferInstance, inferInstance, ?_, one_ne_zero, one_pos, ?_⟩
  · intro m hm
    rw [← Polynomial.C_eq_intCast]
    exact Polynomial.C_ne_zero.2 hm
  · intro p _ K _ _ _ y hy _
    rw [Nat.cast_one, norm_one]
    exact hy _
end Normality
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
