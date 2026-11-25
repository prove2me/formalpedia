-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_h_eq_9af9feb0e0d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:04.628113+00:00
-- url     : https://prove2.me/submissions/443b0410-da94-49c7-b0d8-d89ca66079dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
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
theorem _root_.solution (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    (hz : z ∈ mcPts (dualIdeal b)) :
    (dualLine F b hb).h z = Real.sqrt (∑ j, ‖dualProj b hb (segre z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hp : ∀ j, dualProj b hb (segre z) j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by
    intro j
    simp only [dualProj_apply, segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  show Real.sqrt (dualNormSq b hb _) = _
  congr 1
  rw [dualNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, hp]
  · intro τ _ hτ
    have h0 : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j)) = 0 := funext (hσ τ hτ)
    rw [h0]
    simp
  · simp
end GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
