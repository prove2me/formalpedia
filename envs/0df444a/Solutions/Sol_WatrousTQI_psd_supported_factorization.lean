-- Prove2me | solution 1 for WatrousTQI.psd_supported_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T15:02:16.745204+00:00
-- url     : https://prove2.me/submissions/405e79ff-0d0a-481e-87bb-d58da2eb95d1

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false


theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin m) ℂ) (P : Matrix (Fin n) (Fin n) ℂ) :
    (P.PosSemidef ∧ LinearMap.range P.mulVecLin ≤ LinearMap.range A.mulVecLin) ↔
      ∃ Q : Matrix (Fin m) (Fin m) ℂ, Q.PosSemidef ∧ P = A * Q * Aᴴ := by
  classical
  constructor
  · rintro ⟨hP,hr⟩
    let f := A.mulVecLin
    obtain ⟨g,hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr f.surjective_rangeRestrict)
    obtain ⟨b,hb⟩ := g.exists_extend
    let B : Matrix (Fin m) (Fin n) ℂ := Matrix.toLin'.symm b
    have hB : B.mulVecLin = b := Matrix.toLin'.apply_symm_apply b
    have hs (v : Fin n → ℂ) (hv : v ∈ LinearMap.range A.mulVecLin) : A.mulVec (B.mulVec v) = v := by
      have he := congrArg (fun h : LinearMap.range f →ₗ[ℂ] LinearMap.range f => h ⟨v,hv⟩) hg
      have he' := congrArg Subtype.val he
      have hb' := congrArg (fun h : LinearMap.range f →ₗ[ℂ] (Fin m → ℂ) => h ⟨v,hv⟩) hb
      change A.mulVec (g ⟨v,hv⟩) = v at he'
      change b v = g ⟨v,hv⟩ at hb'
      have hBv := congrArg (fun h : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) => h v) hB
      change B.mulVec v = b v at hBv
      rw [hBv,hb']
      exact he'
    have hAP : A * B * P = P := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      change (A * B * P).mulVec v = P.mulVec v
      rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
      exact hs _ (hr ⟨v,rfl⟩)
    have hPA : P * (A * B)ᴴ = P := by
      have h := congrArg Matrix.conjTranspose hAP
      simpa only [Matrix.conjTranspose_mul,hP.isHermitian.eq] using h
    refine ⟨B * P * Bᴴ,hP.mul_mul_conjTranspose_same B,?_⟩
    symm
    calc
      A * (B * P * Bᴴ) * Aᴴ = (A * B * P) * (A * B)ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = P * (A * B)ᴴ := by rw [hAP]
      _ = P := hPA
  · rintro ⟨Q,hQ,rfl⟩
    refine ⟨hQ.mul_mul_conjTranspose_same A,?_⟩
    rintro v ⟨x,rfl⟩
    refine ⟨(Q * Aᴴ).mulVec x,?_⟩
    change A.mulVec ((Q * Aᴴ).mulVec x) = (A * Q * Aᴴ).mulVec x
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]
