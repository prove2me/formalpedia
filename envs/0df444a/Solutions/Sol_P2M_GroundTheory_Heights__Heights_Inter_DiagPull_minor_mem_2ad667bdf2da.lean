-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_minor_mem_2ad667bdf2da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:01.576337+00:00
-- url     : https://prove2.me/submissions/a1fed6f6-1fc7-4d07-b3a0-3f94d71bc9c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line0_c454c5ab19c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line1_6473e0d79e46

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
theorem _root_.solution (i k : κ) :
    (X ⟨.line0, i⟩ * X ⟨.line1, k⟩ - X ⟨.line0, k⟩ * X ⟨.line1, i⟩ : MRing (T.wwIdx ι ν κ)) ∈
      T.wwIdeal x δ e φ a₀ a₀ := by
  rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, multiConeMap_X_line0, multiConeMap_X_line1,
    multiConeMap_X_line0, multiConeMap_X_line1]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagPull
