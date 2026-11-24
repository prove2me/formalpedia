-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_map_ofReal_88bce7305c00
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:14.106969+00:00
-- url     : https://prove2.me/submissions/d0f2754c-6eaf-4119-9116-b5fd1677a61a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A.map (fun x : ℝ => (x : ℂ))).PosSemidef := by
  have hs : ∀ j k, A k j = A j k := fun j k => by
    simpa using congrFun (congrFun (transpose_of_posSemidef hA) j) k
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext j k
    simp [conjTranspose_apply, hs]
  · set a : ι → ℝ := fun k => (w k).re
    set b : ι → ℝ := fun k => (w k).im
    have ha := quad_nonneg hA a
    have hb := quad_nonneg hA b
    have hre : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).re =
        a ⬝ᵥ (A *ᵥ a) + b ⬝ᵥ (A *ᵥ b) := by
      simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.re_sum, Complex.mul_re,
        Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, a, b, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have him : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im = 0 := by
      have e : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im =
          ∑ j, ∑ k, (w j).re * (A j k * (w k).im) - ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.mul_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.im_sum, Complex.ofReal_re,
          Complex.ofReal_im, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      have hsw : ∑ j, ∑ k, (w j).re * (A j k * (w k).im) =
          ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs]; ring
      rw [e, hsw, sub_self]
    exact Complex.nonneg_iff.mpr ⟨hre ▸ add_nonneg ha hb, him.symm⟩
end GroundTheory.Heights₂.Heights.MCBounds
