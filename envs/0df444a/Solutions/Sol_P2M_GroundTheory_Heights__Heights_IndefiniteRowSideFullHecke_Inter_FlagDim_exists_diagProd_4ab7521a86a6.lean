-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_exists_diagProd_4ab7521a86a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:07:57.921131+00:00
-- url     : https://prove2.me/submissions/41f13a34-b9f6-425f-b022-c519e1cc62cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_toUpper_flagMinorMap_X_200458d87616
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_uMat_colSet_7757b14e6865
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_zero_01f65c540713
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_congr_08f8346d8313

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (j : Fin (n - 1)) :
    ∃ a : UpperQuot F n, Ideal.kerLiftAlg ((toUpper F n).comp (flagMinorMap F n)) a =
      diagProd F n j.val (by omega) := by
  have hj := j.2
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · refine ⟨1, ?_⟩
    rw [map_one, diagProd_congr F n _ (by omega) h0, diagProd_zero]
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, j.val = i + 1 := ⟨j.val - 1, by omega⟩
    refine ⟨Ideal.Quotient.mk _ (X ⟨⟨i, by omega⟩, ⟨colSet i ⟨i, by omega⟩, colSet_card i _ le_rfl⟩⟩), ?_⟩
    rw [Ideal.kerLiftAlg_mk, toUpper_flagMinorMap_X]
    simp only
    rw [flagMinor_uMat_colSet F (n := n) ⟨i, by omega⟩ ⟨i, by omega⟩ le_rfl,
      diagProd_congr F n _ (by omega) hi, diagProd_succ]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
