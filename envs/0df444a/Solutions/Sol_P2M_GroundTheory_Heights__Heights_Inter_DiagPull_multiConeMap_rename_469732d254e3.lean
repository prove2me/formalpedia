-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_rename_469732d254e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:45.941197+00:00
-- url     : https://prove2.me/submissions/acef2738-d25b-4ba2-9368-c3ff35ee41a8

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
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution (j : Fin 2) (s : MRing (T.yyIdx ι ν κ)) :
    T.multiConeMap (T.wwCoord x δ e φ a₀ a₀) (rename (T.yyEmb j) s) =
      eval₂ (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q) * X (blk j q.1)) s := by
  rw [T.multiConeMap, coe_eval₂Hom, eval₂_rename]
  congr 1
  funext q
  obtain ⟨b, i⟩ := q
  fin_cases j <;> cases b <;> rfl
end GroundTheory.Heights₂.Heights.Inter.DiagPull
