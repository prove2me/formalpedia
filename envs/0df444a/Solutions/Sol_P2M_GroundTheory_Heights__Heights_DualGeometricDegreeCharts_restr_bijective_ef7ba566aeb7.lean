-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_restr_bijective_ef7ba566aeb7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:40.677625+00:00
-- url     : https://prove2.me/submissions/f9f471e0-37c8-4bc5-8283-cee782200e76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts

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
namespace GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
theorem _root_.solution (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Function.Bijective (Ψ ∘ₗ planeLin b σ) := by
  have hinj : Function.Injective (Ψ ∘ₗ planeLin b σ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra h0
    exact hΨ _ (hOf K (D + 1) F T b hb σ v h0) hv
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
end GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
