-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_fibre_eq_0dc2611b461d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:31.027807+00:00
-- url     : https://prove2.me/submissions/c5c02ee0-2a07-482a-a892-7f30bdda7f26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_proj_segre_planePt_9c8c7cf829ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
theorem _root_.solution (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) {D : ℕ}
    {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    fibre (dualIdeal b) (dualProj b hb) y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : dualRecover b hb (fun t => z ⟨(), t⟩) =
        dualRecover b hb (fun t => dualPlanePt b σ (Fin.cons 1 y) ⟨(), t⟩) := by
      rw [recover_planePt]
      funext ⟨τ, j⟩
      by_cases hτ : τ = σ
      · subst hτ
        rw [if_pos rfl, ← hΨ]
        simp only [dualProj_apply, segre_const]
        exact (Finset.sum_eq_single τ (fun τ' _ h' => hσ τ' h' j) (by simp)).symm
      · rw [if_neg hτ]
        exact hσ τ hτ j
    have h1 := (dualRecover b hb).injective hW
    funext ⟨u, t⟩
    cases u
    exact (congrFun h1 t).symm
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) F T b hb σ _ hv, rfl, proj_segre_planePt b hb σ _⟩
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
