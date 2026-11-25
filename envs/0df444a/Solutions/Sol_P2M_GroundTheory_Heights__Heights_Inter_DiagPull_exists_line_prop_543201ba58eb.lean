-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_exists_line_prop_543201ba58eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:04.335353+00:00
-- url     : https://prove2.me/submissions/eed82051-20a7-4afd-912c-a36a2dc7945a

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
theorem _root_.solution {z : (Σ k, T.wwIdx ι ν κ k) → ℂ} (hz : z ∈ mcPts (T.wwIdeal x δ e φ a₀ a₀)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩ := by
  have hmin : ∀ i k : κ, z ⟨.line0, i⟩ * z ⟨.line1, k⟩ - z ⟨.line0, k⟩ * z ⟨.line1, i⟩ = 0 := by
    intro i k
    have := hz.2 _ (minor_mem x δ e φ a₀ i k)
    simpa using this
  obtain ⟨i, hi⟩ := hz.1 .line0
  obtain ⟨j, hj⟩ := hz.1 .line1
  have hi' : z ⟨.line0, i⟩ ≠ 0 := hi
  have hk : ∀ k : κ, z ⟨.line1, k⟩ = z ⟨.line1, i⟩ / z ⟨.line0, i⟩ * z ⟨.line0, k⟩ := by
    intro k
    have h := hmin i k
    field_simp
    linear_combination h
  refine ⟨z ⟨.line1, i⟩ / z ⟨.line0, i⟩, fun h0 => hj ?_, hk⟩
  rw [hk j, h0, zero_mul]
end GroundTheory.Heights₂.Heights.Inter.DiagPull
