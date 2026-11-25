-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_range_544901a4c07b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:21:59.894907+00:00
-- url     : https://prove2.me/submissions/e4434668-37cb-436c-9a1a-4eea276d8a9a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_polynomial_a210957d600c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_isAlgebraic_range_b1cc57e8997d

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
variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution :
    trdeg k (dehom (k := k) y hi₀).range = trdeg k (ratioRing (k := k) y) + 1 := by
  have := isAlgebraic_range (k := k) y hi₀
  have : FaithfulSMul k (dehom (k := k) y hi₀).range :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  have := (faithfulSMul_iff_algebraMap_injective (dehom (k := k) y hi₀).range
    (Polynomial (ratioRing (k := k) y))).2 Subtype.val_injective
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  rw [← trdeg_polynomial (k := k) (ratioRing (k := k) y), ← trdeg_add_eq k (dehom (k := k) y hi₀).range
    (A := Polynomial (ratioRing (k := k) y)),
    trdeg_eq_zero (R := (dehom (k := k) y hi₀).range) (A := Polynomial (ratioRing (k := k) y)),
    add_zero]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
