-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_notMem_25089793c224
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:58.524388+00:00
-- url     : https://prove2.me/submissions/1ea8b56c-0e17-481d-96aa-1bb8d9eff43a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_minor_mem_2ad667bdf2da

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
theorem _root_.solution {W : Ideal (MRing (T.wwIdx ι ν κ))} (hW : W.IsPrime)
    (hΔ : T.wwIdeal x δ e φ a₀ a₀ ≤ W) (hrel : IsRelevant W) :
    ∃ k : κ, (X ⟨.line0, k⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧ (X ⟨.line1, k⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := by
  obtain ⟨i, hi⟩ := hrel .line0
  obtain ⟨j, hj⟩ := hrel .line1
  refine ⟨i, hi, fun h => ?_⟩
  have hm := hΔ (minor_mem x δ e φ a₀ i j)
  have h2 : (X ⟨.line0, j⟩ * X ⟨.line1, i⟩ : MRing (T.wwIdx ι ν κ)) ∈ W := W.mul_mem_left _ h
  have h3 : (X ⟨.line0, i⟩ * X ⟨.line1, j⟩ : MRing (T.wwIdx ι ν κ)) ∈ W := by
    have e' : (X ⟨.line0, i⟩ * X ⟨.line1, j⟩ : MRing (T.wwIdx ι ν κ)) =
        (X ⟨.line0, i⟩ * X ⟨.line1, j⟩ - X ⟨.line0, j⟩ * X ⟨.line1, i⟩) + X ⟨.line0, j⟩ * X ⟨.line1, i⟩ := by
      ring
    rw [e']
    exact W.add_mem hm h2
  rcases hW.mem_or_mem h3 with h4 | h4
  · exact hi h4
  · exact hj h4
end GroundTheory.Heights₂.Heights.Inter.DiagPull
