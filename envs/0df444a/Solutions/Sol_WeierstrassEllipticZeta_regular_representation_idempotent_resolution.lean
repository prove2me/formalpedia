-- Prove2me | solution 1 for WeierstrassEllipticZeta.regular_representation_idempotent_resolution
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T17:57:18.686636+00:00
-- url     : https://prove2.me/submissions/c77cc372-093d-49da-8aa5-15e666cebc99

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Ring.Idempotent

open scoped Classical



theorem solution
    (R B n ι : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [Fintype n] [DecidableEq n] [Fintype ι]
    (β : Module.Basis n R B) (P : ι → Module.End R (n → R))
    (hcomm : ∀ (a : B) (i : ι),
      Commute (P i) (Algebra.leftMulMatrix β a).mulVecLin)
    (hidem : ∀ i, IsIdempotentElem (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : (∑ i, P i) = 1) :
    ∃ ε : ι → B,
      (∀ i, (Algebra.leftMulMatrix β (ε i)).mulVecLin = P i) ∧
      (∀ i, ε i = β.equivFun.symm (P i (β.equivFun 1))) ∧
      (∀ i, IsIdempotentElem (ε i)) ∧
      (∀ i j, i ≠ j → ε i * ε j = 0) ∧
      (∑ i, ε i) = 1 := by
  classical
  let ρ : B →ₐ[R] Module.End R (n → R) :=
    Matrix.toLinAlgEquiv'.toAlgHom.comp (Algebra.leftMulMatrix β)
  have hact (a x : B) : ρ a (β.equivFun x) = β.equivFun (a * x) :=
    Algebra.leftMulMatrix_mulVec_repr β a x
  have hfaith : Function.Injective ρ :=
    Matrix.toLinAlgEquiv'.injective.comp (Algebra.leftMulMatrix_injective β)
  let ε : ι → B := fun i => β.equivFun.symm (P i (β.equivFun 1))
  have heval (i : ι) : β.equivFun (ε i) = P i (β.equivFun 1) :=
    β.equivFun.apply_symm_apply _
  have hρeq (i : ι) : ρ (ε i) = P i := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := β.equivFun.surjective v
    have h := DFunLike.congr_fun (hcomm x i).eq (β.equivFun 1)
    change P i (ρ x (β.equivFun 1)) = ρ x (P i (β.equivFun 1)) at h
    rw [hact, mul_one, ← heval, hact] at h
    rw [hact, mul_comm (ε i) x]
    exact h.symm
  refine ⟨ε, hρeq, fun _ => rfl, ?_, ?_, ?_⟩
  · intro i
    apply hfaith
    rw [map_mul, hρeq]
    exact hidem i
  · intro i j hij
    apply hfaith
    rw [map_mul, map_zero, hρeq, hρeq]
    exact horth i j hij
  · apply hfaith
    rw [map_sum, map_one]
    simpa only [hρeq] using hsum

