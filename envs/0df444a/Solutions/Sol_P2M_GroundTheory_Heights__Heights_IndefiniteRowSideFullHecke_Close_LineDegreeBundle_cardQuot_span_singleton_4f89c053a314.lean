-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_cardQuot_span_singleton_4f89c053a314
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:06.824957+00:00
-- url     : https://prove2.me/submissions/2a0b9600-7ae8-43bc-853c-20c8965c75a4

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
theorem _root_.solution {L : Type*} [Field L] [NumberField L] (a : 𝓞 L) :
    (Submodule.cardQuot (Ideal.span {a} : Ideal (𝓞 L)) : ℝ) = |(Algebra.norm ℚ (a : L) : ℝ)| := by
  rw [← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Rat.cast_intCast, Algebra.coe_norm_int]
end LineDegreeBundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
