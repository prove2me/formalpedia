-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_X_mem_diag_iff_cd110d0e6e0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:23.71775+00:00
-- url     : https://prove2.me/submissions/2152d6f9-cb3e-4acb-81d1-c1039a1bcf0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
theorem _root_.solution {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
    (p : Σ k, T.wwIdx ι ν κ k) :
    (X p : MRing (T.wwIdx ι ν κ)) ∈ T.wwIdeal x δ e φ a₀ a₀ ↔ T.wwCoord x δ e φ a₀ a₀ p = 0 := by
  show X p ∈ RingHom.ker _ ↔ _
  rw [RingHom.mem_ker, T.multiConeMap, eval₂Hom_X', mul_eq_zero, C_eq_zero]
  simp [X_ne_zero]
end GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
