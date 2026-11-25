-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_funField_2422b22669ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:50.698616+00:00
-- url     : https://prove2.me/submissions/d9621371-c0a2-4ef0-83f4-d9b594b5eaba

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution (y : Fin (N + 1) → Ω) :
    trdeg k (funField (k := k) y) = trdeg k (ratioRing (k := k) y) := by
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  show trdeg k (IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}) = _
  rw [← trdeg_add_eq k (ratioRing (k := k) y)
    (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}),
    trdeg_eq_zero (R := ratioRing (k := k) y)
      (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}), add_zero]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
