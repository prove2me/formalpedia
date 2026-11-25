-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_primeOf_eq_ker_7df1ef8391e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:29.935169+00:00
-- url     : https://prove2.me/submissions/50735c2e-325f-4483-87f6-793f983b2b04

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_injective_aa61db869d27
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_comp_dehom_238d65ec5abd

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
theorem _root_.solution : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀) := by
  ext f
  rw [primeOf_eq, RingHom.mem_ker, RingHom.mem_ker, ← rehom_comp_dehom (k := k) y hi₀, AlgHom.comp_apply,
    map_eq_zero_iff _ (rehom_injective (k := k) y hi₀)]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
