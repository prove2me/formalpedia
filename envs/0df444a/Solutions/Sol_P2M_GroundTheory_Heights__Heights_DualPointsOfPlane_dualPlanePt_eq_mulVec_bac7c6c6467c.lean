-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_dualPlanePt_eq_mulVec_bac7c6c6467c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:20.207993+00:00
-- url     : https://prove2.me/submissions/a35842c2-afb5-4a4a-9cff-463789068ad7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointsOfPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualPointsOfPlane
theorem _root_.solution [DecidableEq (K →+* ℂ)] (b : Module.Basis T ℤ (dualLattice F))
    (σ : K →+* ℂ) (v : Fin i → ℂ) (t : T) :
    dualPlanePt b σ v ⟨(), t⟩ =
      (dualEmbMatrix b *ᵥ fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) t := by
  simp only [dualPlanePt, mulVec, dotProduct, dualEmbMatrix, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single σ]
  · simp
  · intro τ hτ
    simp [hτ]
end GroundTheory.Heights₂.Heights.DualPointsOfPlane
