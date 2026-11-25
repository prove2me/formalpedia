-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_tendsto_finsum_of_finite_286d3c22c625
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:30.823986+00:00
-- url     : https://prove2.me/submissions/cc581b47-376b-4185-b7ee-a107422745d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {α : Type*} {p : α → Prop} (hp : {W | p W}.Finite) {f : ℝ → α → ℝ}
    {g : α → ℝ} {l : Filter ℝ} (h : ∀ W, p W → Tendsto (fun ε => f ε W) l (𝓝 (g W))) :
    Tendsto (fun ε => ∑ᶠ (W) (_ : p W), f ε W) l (𝓝 (∑ᶠ (W) (_ : p W), g W)) := by
  have e : ∀ u : α → ℝ, ∑ᶠ (W) (_ : p W), u W = ∑ W ∈ hp.toFinset, u W :=
    fun u => finsum_mem_eq_finite_toFinset_sum u hp
  have e1 : (fun ε => ∑ᶠ (W) (_ : p W), f ε W) = fun ε => ∑ W ∈ hp.toFinset, f ε W :=
    funext fun ε => e (f ε)
  rw [e1, e g]
  exact tendsto_finsetSum _ fun W hW => h W (hp.mem_toFinset.mp hW)
end GroundTheory.Heights₂.Heights.Inter
