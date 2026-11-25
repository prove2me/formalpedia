-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_diagonalPullback_secondLine_eq_759650f7ce4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:20.75652+00:00
-- url     : https://prove2.me/submissions/69fb3a3a-d9f8-4be2-b478-954f8dabb5d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull

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
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
omit [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution {z : (Σ k, T.wwIdx ι ν κ k) → ℂ} {c : ℂ} (hk : ∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) :
    (fun p => z (T.yyEmb 1 p)) = fun p => lineScal c p.1 * z (T.yyEmb 0 p) := by
  funext p
  obtain ⟨b, i⟩ := p
  cases b
  · simp [T.yyEmb, lineScal]
  · simp [T.yyEmb, lineScal]
  · exact hk i
end GroundTheory.Heights₂.Heights.Inter.DiagPull
