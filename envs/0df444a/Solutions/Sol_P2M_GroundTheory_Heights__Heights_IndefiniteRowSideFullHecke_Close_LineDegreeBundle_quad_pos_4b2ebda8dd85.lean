-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_pos_4b2ebda8dd85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:10.852601+00:00
-- url     : https://prove2.me/submissions/a124b0d2-7060-4863-864b-19e3c185b41c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace LineDegreeBundle
theorem _root_.solution {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) {u : Fin n → ℂ}
    (hu : u ≠ 0) :
    ‖star u ⬝ᵥ (H *ᵥ u)‖ = (star u ⬝ᵥ (H *ᵥ u)).re ∧ 0 < (star u ⬝ᵥ (H *ᵥ u)).re := by
  have h := hH.dotProduct_mulVec_pos hu
  obtain ⟨hre, him⟩ := Complex.lt_def.mp h
  have hQ : star u ⬝ᵥ (H *ᵥ u) = ((star u ⬝ᵥ (H *ᵥ u)).re : ℂ) :=
    Complex.ext rfl (by simp only [Complex.ofReal_im]; rw [← him]; rfl)
  refine ⟨?_, by simpa using hre⟩
  conv_lhs => rw [hQ]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]
end LineDegreeBundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
