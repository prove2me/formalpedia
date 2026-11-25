-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_comp_dehom_238d65ec5abd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:46.685798+00:00
-- url     : https://prove2.me/submissions/7e841580-875f-4399-9b22-02bbe0548a2d

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
variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution : (rehom (k := k) y i₀).comp (dehom y hi₀) = cone (S := k) y := by
  refine MvPolynomial.algHom_ext fun j => ?_
  have hc : (cone (S := k) y) (X j) = Polynomial.C (y j) * Polynomial.X := by
    simp [cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rw [hc]
  simp [rehom, dehom, ratio]
  rw [← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ hi₀]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
