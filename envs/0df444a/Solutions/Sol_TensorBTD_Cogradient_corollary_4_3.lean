-- Prove2me | solution 1 for TensorBTD.Cogradient.corollary_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:18:25.53719+00:00
-- url     : https://prove2.me/submissions/34f1cdaa-7e25-428d-92bf-f8f2092ec9ad

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting
set_option autoImplicit false
open TensorBTD.Cogradient
open Matrix

theorem solution {P Q : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {K : Type*} [Fintype K]
    (σ : Finset (Fin P ⊕ Fin Q)) (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) K ℂ) :
    (V σ A)ᴴ * V σ A = W σ A := by
  classical
  ext c c'
  have h1 : ∀ ρ : KRIdx I σ, (starRingEnd ℂ) (V σ A ρ c) * V σ A ρ c' =
      ∏ m : {m : Fin P ⊕ Fin Q // m ∉ σ},
        (starRingEnd ℂ) (A m.1 (ρ m) c) * A m.1 (ρ m) c' := by
    intro ρ
    simp only [V, map_prod, ← Finset.prod_mul_distrib]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun m : {m : Fin P ⊕ Fin Q // m ∉ σ} => (Finset.univ : Finset (Fin (I m.1))))
    (fun m i => (starRingEnd ℂ) (A m.1 i c) * A m.1 i c')
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  unfold W
  rw [Finset.prod_subtype (Finset.univ.filter (· ∉ σ)) (p := (· ∉ σ)) (by simp)]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
