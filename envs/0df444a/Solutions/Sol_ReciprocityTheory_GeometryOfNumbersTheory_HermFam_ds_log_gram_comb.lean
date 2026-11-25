-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_log_gram_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:23:33.486252+00:00
-- url     : https://prove2.me/submissions/3a696e1d-4a55-4546-86c4-5a45ae810914

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_gram_det_re_pos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_gram_comb_det_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
namespace HermFam
theorem _root_.solution (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (G : Matrix (Fin r) (Fin r) K) (hG : G.det ≠ 0) :
    Real.log (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Real.log (Complex.normSq (σ G.det)) + Real.log (h.gram σ v).det.re := by
  rw [h.ds_gram_comb_det_re, Real.log_mul]
  · exact (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hG)).ne'
  · exact (h.ds_gram_det_re_pos σ hv).ne'
end HermFam
end ReciprocityTheory.GeometryOfNumbersTheory
