-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_sum_log_norm_e180af1d2243
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:13.70473+00:00
-- url     : https://prove2.me/submissions/eeb6feb1-316b-49c1-8045-00d4c2d34a4b

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
theorem _root_.solution {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ ↦ ‖φ x‖)
    (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]
end LineDegreeBundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
