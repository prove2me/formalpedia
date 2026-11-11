-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.triangle_lattice_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:16:38.340723+00:00
-- url     : https://prove2.me/submissions/d65dc86b-fd88-428a-8154-4c90078fb75b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleUnitDirection_norm
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleAltitudeVector_norm_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleLatticeAnchor_first
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleLatticeAnchor_second
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_unit_inner_coordinate_bound
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_shear_lattice_card_le_pi
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (s : Finset (ℤ × ℤ)) (o b c z : E) {ell : ℝ}
    (hell : 0 < ell) (hb : b ≠ 0) (hc : triangleAltitudeVector b c ≠ 0)
    (hbL : ‖b‖ ≤ ell) (hcL : ‖c‖ ≤ ell)
    (hmem : ∀ p ∈ s, dist (triangleLatticeAnchor o b c ell p) z ≤ 2) :
    (s.card : ℝ) ≤ 8 * Real.pi * ell ^ 2 / (‖b‖ * ‖triangleAltitudeVector b c‖) := by
  have hbp : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hcp : 0 < ‖triangleAltitudeVector b c‖ := norm_pos_iff.mpr hc
  have hbound := shear_lattice_card_le_pi s (div_pos hbp hell) (div_pos hcp hell)
    ((div_le_one hell).2 hbL)
    ((div_le_one hell).2 ((triangleAltitudeVector_norm_le hb).trans hcL))
    (c := ⟪triangleUnitDirection b, c⟫_ℝ / ell)
    (x := ⟪triangleUnitDirection b, z - o⟫_ℝ)
    (y := ⟪triangleUnitDirection (triangleAltitudeVector b c), z - o⟫_ℝ)
    (fun p hp => by
      rw [← triangleLatticeAnchor_first o b c ell p hb]
      exact unit_inner_coordinate_bound _ _ _ _ (triangleUnitDirection_norm hb) (hmem p hp))
    (fun p hp => by
      rw [← triangleLatticeAnchor_second o b c ell p hb hc]
      exact unit_inner_coordinate_bound _ _ _ _ (triangleUnitDirection_norm hc) (hmem p hp))
  convert hbound using 1 <;> field_simp [hell.ne', hbp.ne', hcp.ne'] <;> ring
end QEC.Coding.BDL26ReplacementEmbedding
