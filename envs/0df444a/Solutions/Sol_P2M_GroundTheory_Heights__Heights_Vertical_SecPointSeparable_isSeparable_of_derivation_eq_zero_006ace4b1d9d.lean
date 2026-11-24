-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_isSeparable_of_derivation_eq_zero_006ace4b1d9d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:47.700834+00:00
-- url     : https://prove2.me/submissions/11ba0f24-9bec-4111-b6b2-c4716af710d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenericFormsKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecPointSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecPointSeparable
namespace GroundTheory.Heights₂.Heights.Vertical.SecPointSeparable
theorem _root_.solution {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨⟨fun a b => ?_⟩⟩
  have key : ∀ ω : Ω[L⁄K], ω = 0 := by
    intro ω
    refine (Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_
    have : φ = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation K L).injective
      rw [map_zero]
      exact h _
    rw [this, LinearMap.zero_apply]
  rw [key a, key b]
end GroundTheory.Heights₂.Heights.Vertical.SecPointSeparable
