-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_injective_aa61db869d27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:14.164552+00:00
-- url     : https://prove2.me/submissions/02ae0363-9d87-447b-988e-5dca94c363c2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_aeval_C_mul_X_injective_c5ce1551daa7

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
include hi₀
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution : Function.Injective (rehom (k := k) y i₀) := by
  rw [rehom, AlgHom.coe_comp]
  exact (aeval_C_mul_X_injective hi₀).comp (Polynomial.map_injective _ Subtype.val_injective)
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
