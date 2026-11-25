-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_isGoodProj_9122b7c98d31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:11.155361+00:00
-- url     : https://prove2.me/submissions/b5753351-5d2d-4280-846d-ec27f9603223

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreePositive_segre_apply_0b8426073082
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
namespace GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
theorem _root_.solution (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by
  intro z hz h0
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hne : dualRecover b hb (fun t => z ⟨(), t⟩) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hz.1 ()
    exact ht (congrFun ((dualRecover b hb).map_eq_zero_iff.mp h) t)
  obtain ⟨⟨τ, j⟩, hτ⟩ := Function.ne_iff.mp hne
  have hτσ : τ = σ := by
    by_contra h
    exact hτ (hσ τ h j)
  subst hτσ
  have h1 := congrFun h0 j
  rw [dualProj_apply] at h1
  simp only [segre_apply] at h1
  rw [Finset.sum_eq_single τ (fun τ' _ h => hσ τ' h j) (fun h => absurd (Finset.mem_univ τ) h)] at h1
  exact hτ h1
end GroundTheory.Heights₂.Heights.DualGeometricDegreePositive
