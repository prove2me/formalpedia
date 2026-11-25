-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_aeval_X_det_505467d04c1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:01.134847+00:00
-- url     : https://prove2.me/submissions/51d8c349-e4e1-4bbd-8dfc-092f88af6565

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
omit [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (l : ν) : aeval (T.wwCoord x δ e φ a₀ a₁) (X ⟨T.WBlk.det, l⟩ : MRing (T.wwIdx ι ν κ)) =
      algebraMap Ω Φ (δ l) := by
  rw [aeval_X]; rfl
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
