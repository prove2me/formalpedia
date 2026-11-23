-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.idemGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.651974+00:00
-- url     : https://prove2.me/submissions/4203c440-21d1-4249-b783-3f882f91721e

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : IdemGenStatement := by
  rintro R _ g d P hP ⟨e⟩

  let L : (Fin g → R) →ₗ[R] (Fin d → R) := e.toLinearMap ∘ₗ (mulVecLin P).rangeRestrict
  let T : (Fin d → R) →ₗ[R] (Fin g → R) :=
    (LinearMap.range (mulVecLin P)).subtype ∘ₗ e.symm.toLinearMap
  obtain ⟨M, hLM⟩ : ∃ M : Matrix (Fin d) (Fin g) R, Matrix.toLin' M = L :=
    ⟨_, Matrix.toLin'_toMatrix' L⟩
  obtain ⟨N, hTN⟩ : ∃ N : Matrix (Fin g) (Fin d) R, Matrix.toLin' N = T :=
    ⟨_, Matrix.toLin'_toMatrix' T⟩

  have hPNM : P = N * M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM, hTN]
    refine LinearMap.ext fun x => ?_
    simp [L, T, Matrix.toLin'_apply]

  have hMP : M * P = M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, L, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hP]

  have hrow : ∀ i, Pᵀ *ᵥ M i = M i := by
    intro i
    funext j
    have h := congrFun (congrFun hMP i) j
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine ⟨fun i => ⟨M i, LinearMap.mem_range.mpr ⟨M i, by rw [Matrix.mulVecLin_apply]; exact hrow i⟩⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw

  have key : mulVecLin Pᵀ v = ∑ i, (Nᵀ *ᵥ v) i • M i := by
    rw [Matrix.mulVecLin_apply, hPNM, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨fun i => (Nᵀ *ᵥ v) i, ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact key.symm
end ReciprocityTheory.PGsh.Up
