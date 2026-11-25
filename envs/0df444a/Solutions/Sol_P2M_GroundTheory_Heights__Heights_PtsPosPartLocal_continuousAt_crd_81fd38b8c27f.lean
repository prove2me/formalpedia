-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuousAt_crd_81fd38b8c27f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:46.520002+00:00
-- url     : https://prove2.me/submissions/346156fe-a0bc-4456-9f7f-64d645babf9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_eq_09384b5146ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_differentiableAt_coord_664cafcb5a8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {w : ((k : K) → ι k) → ℂ} (hw : Ψ w 0 ≠ 0) : ContinuousAt (crd Ψ) w := by
  have h : DifferentiableAt ℂ (fun w (i : Fin e) => (Ψ w 0)⁻¹ * Ψ w i.succ) w :=
    differentiableAt_pi.mpr fun i =>
      (DifferentiableAt.inv (h := fun x => Ψ x 0) (differentiableAt_coord w 0) hw).mul
        (differentiableAt_coord w i.succ)
  have heq : crd Ψ = fun w (i : Fin e) => (Ψ w 0)⁻¹ * Ψ w i.succ := funext crd_eq
  rw [heq]
  exact h.continuousAt
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
