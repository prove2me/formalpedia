-- Prove2me | solution 1 for QuantumFiniteSpectral.orthonormal_spectrum_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:50:28.835377+00:00
-- url     : https://prove2.me/submissions/486c82ae-85ee-4ae2-a2be-ad5f1f815feb

import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

set_option autoImplicit false

theorem solution {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K] (J : Matrix I I ℂ) (v : K → I → ℂ) (e : K → ℂ)
    (horth : ∀ k l, (∑ i, conj (v k i) * v l i) = if k = l then 1 else 0)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (heig : ∀ k, J.mulVec (v k) = e k • v k) :
    Jᴴ * J = J * Jᴴ ∧ (J.PosSemidef ↔ ∀ k, 0 ≤ e k) ∧ Matrix.trace J = ∑ k, e k := by
  classical
  let V : Matrix I K ℂ := fun i k => v k i
  let D : Matrix K K ℂ := Matrix.diagonal e
  have hVV : Vᴴ * V = 1 := by
    ext k l
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,V,Matrix.one_apply,Complex.star_def] using horth k l
  have hcol : V.col = v := rfl
  have hrange : LinearMap.range V.mulVecLin = ⊤ := by
    simpa only [Matrix.range_mulVecLin,hcol] using hspan
  have hsurj : Function.Surjective V.mulVecLin := LinearMap.range_eq_top.mp hrange
  have hVh : V * Vᴴ = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := hsurj x
    have hy : Vᴴ.mulVec (V.mulVec y) = y := by rw [Matrix.mulVec_mulVec,hVV,Matrix.one_mulVec]
    change (V * Vᴴ).mulVec (V.mulVec y) = (1 : Matrix I I ℂ).mulVec (V.mulVec y)
    rw [← Matrix.mulVec_mulVec,hy,Matrix.one_mulVec]
  have hJV : J * V = V * D := by
    ext i k
    have h := congrArg (fun w : I → ℂ => w i) (heig k)
    simpa [V,D,Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.diagonal,smul_eq_mul,mul_comm] using h
  have hJ : J = V * D * Vᴴ := by
    calc
      J = J * (V * Vᴴ) := by rw [hVh,Matrix.mul_one]
      _ = (J * V) * Vᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hJV]
  have hprod (A B : Matrix K K ℂ) :
      (V * A * Vᴴ) * (V * B * Vᴴ) = V * (A * B) * Vᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V (B * Vᴴ),hVV,Matrix.one_mul]
  have hstar : Jᴴ = V * Dᴴ * Vᴴ := by
    simp only [hJ,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  have hdcomm : Dᴴ * D = D * Dᴴ := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  refine ⟨?_,?_,?_⟩
  · rw [hstar,hJ,hprod,hprod,hdcomm]
  · have hback : Vᴴ * J * V = D := by
      rw [hJ]
      calc
        _ = (Vᴴ * V) * D * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = D := by rw [hVV,Matrix.one_mul,Matrix.mul_one]
    constructor
    · intro hp
      have h := hp.conjTranspose_mul_mul_same V
      rw [hback] at h
      exact Matrix.posSemidef_diagonal_iff.mp h
    · intro hp
      have hd : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hp
      rw [hJ]
      exact hd.mul_mul_conjTranspose_same V
  · rw [hJ,Matrix.trace_mul_cycle,hVV,Matrix.one_mul]
    simp [D,Matrix.trace]