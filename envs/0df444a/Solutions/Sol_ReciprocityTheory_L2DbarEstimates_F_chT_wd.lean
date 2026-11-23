-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_wd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:46.725086+00:00
-- url     : https://prove2.me/submissions/116e81a8-d77c-4102-bf60-4b9da9f46c69

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (ρ : V n → ℝ) (φ : V n → ℂ) (O : Set (V n)) (hOo : IsOpen O)
    (h1 : ∀ y ∈ O, ρ y = 1) (y : V n) (hy : y ∈ O) (j : Fin n) :
    wd n j (fun y => (ρ y : ℂ) * φ y) y = wd n j φ y ∧
      wdb n j (fun y => (ρ y : ℂ) * φ y) y = wdb n j φ y := by
  have hev : (fun y => (ρ y : ℂ) * φ y) =ᶠ[𝓝 y] φ := by
    filter_upwards [hOo.mem_nhds hy] with w hw
    rw [h1 w hw]; simp
  have := hev.fderiv_eq (𝕜 := ℝ)
  unfold wd wdb
  rw [this]
  exact ⟨rfl, rfl⟩
end ReciprocityTheory.L2DbarEstimates.F
