-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:58.363888+00:00
-- url     : https://prove2.me/submissions/7c850f2d-0e4d-417c-914f-346a9dace27e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane

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
open GroundTheory.Heights₂.Heights.DualPointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.DualPointsOnPlane
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s : T) (j : Fin i) :
    ∑ t, (mulMat b α s t : K) * (b t : Fin i → K) j = (α : K) * (b s : Fin i → K) j := by
  have h := b.sum_repr ⟨(α : K) • (b s : Fin i → K), smul_mem_dualLattice α (b s).2⟩
  have h2 := congrArg (fun v : dualLattice F => (v : Fin i → K) j) h
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
    zsmul_eq_mul, smul_eq_mul] at h2
  exact h2
end GroundTheory.Heights₂.Heights.DualPointsOnPlane
