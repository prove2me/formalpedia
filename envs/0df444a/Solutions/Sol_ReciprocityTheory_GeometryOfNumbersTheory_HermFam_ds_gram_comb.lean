-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_gram_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:20.82915+00:00
-- url     : https://prove2.me/submissions/6cf5b76f-66b2-4a22-a4a4-96b6573ccc97

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_form_sum_right
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_form_sum_left
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_form_smul_left

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
    h.gram σ (fun j => ∑ i, G i j • v i) = (G.map σ)ᴴ * h.gram σ v * G.map σ := by
  ext a b
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right,
    Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end HermFam
end ReciprocityTheory.GeometryOfNumbersTheory
