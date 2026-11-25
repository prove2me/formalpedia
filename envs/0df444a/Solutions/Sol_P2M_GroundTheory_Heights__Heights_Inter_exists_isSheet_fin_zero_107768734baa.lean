-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_exists_isSheet_fin_zero_107768734baa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:05.465793+00:00
-- url     : https://prove2.me/submissions/78bba209-95e2-4d8a-84c3-c16af9bb2dd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : ∃ γ, IsSheet P Ψ y w γ := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  refine ⟨fun _ => z, rfl, Eventually.of_forall fun y' => ⟨differentiableAt_const _, hz, ?_⟩⟩
  rw [Subsingleton.elim y' y]
  exact hΨ
end GroundTheory.Heights₂.Heights.Inter
