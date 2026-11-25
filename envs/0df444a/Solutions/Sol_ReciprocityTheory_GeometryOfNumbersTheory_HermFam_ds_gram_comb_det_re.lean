-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_gram_comb_det_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:18.784721+00:00
-- url     : https://prove2.me/submissions/efe10055-c961-4aa7-bde9-342a6be9659e

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_gram_comb

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
theorem _root_.solution (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Complex.normSq (σ G.det) * (h.gram σ v).det.re := by
  rw [h.ds_gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, RingHom.map_det]
  have : star (σ.mapMatrix G).det * (h.gram σ v).det * (σ.mapMatrix G).det =
      (Complex.normSq (σ.mapMatrix G).det : ℂ) * (h.gram σ v).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
  rw [RingHom.mapMatrix_apply] at this ⊢
  rw [this, Complex.re_ofReal_mul]
end HermFam
end ReciprocityTheory.GeometryOfNumbersTheory
