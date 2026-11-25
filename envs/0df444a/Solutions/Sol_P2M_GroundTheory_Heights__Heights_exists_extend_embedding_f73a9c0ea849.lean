-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_extend_embedding_f73a9c0ea849
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:44.514478+00:00
-- url     : https://prove2.me/submissions/0463faa9-693c-44b4-a7e5-2a9659e44cfa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (τ : L →+* ℂ) :
    ∃ σ : AlgebraicClosure ℚ →+* ℂ, ∀ a : L, σ a = τ a := by
  let : Algebra L ℂ := τ.toAlgebra
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact ⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).toRingHom, fun a ↦
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).commutes a⟩
end GroundTheory.Heights₂.Heights
