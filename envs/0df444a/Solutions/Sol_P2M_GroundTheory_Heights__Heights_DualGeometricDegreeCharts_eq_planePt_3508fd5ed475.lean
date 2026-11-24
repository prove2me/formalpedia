-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_eq_planePt_3508fd5ed475
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:40.684244+00:00
-- url     : https://prove2.me/submissions/8ddd4acb-ca5b-461a-ae9b-8a57c484be7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e


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
open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
open StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    {σ : K →+* ℂ} (hσ : ∀ τ : K →+* ℂ, τ ≠ σ → ∀ j, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) = 0) :
    z = dualPlanePt b σ (recLin b hb σ z) := by
  have hW : dualRecover b hb (fun t => z ⟨(), t⟩) =
      dualRecover b hb (fun t => dualPlanePt b σ (recLin b hb σ z) ⟨(), t⟩) := by
    rw [recover_planePt]
    funext ⟨τ, j⟩
    by_cases hτ : τ = σ
    · subst hτ
      rw [if_pos rfl]
      rfl
    · rw [if_neg hτ]
      exact hσ τ hτ j
  have h1 := (dualRecover b hb).injective hW
  funext ⟨u, t⟩
  cases u
  exact congrFun h1 t
end GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
