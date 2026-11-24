-- Prove2me | solution 1 for WeilConjectures.exists_linearEquiv_conj_eq_dualTranspose
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:07:10.165808+00:00
-- url     : https://prove2.me/submissions/c7765d6e-21aa-4fa9-a6dd-3b81661aa974
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_similar_to_transpose

/-!
Transport matrix transpose-similarity to a dual-transpose conjugator via a finite basis
and `Basis.toDualEquiv`.
-/

open Module Matrix

theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : V →ₗ[K] V) :
    ∃ (d : V ≃ₗ[K] Module.Dual K V),
      d.conj B = B.dualMap := by
  classical
  let b := Module.Free.chooseBasis K V
  let A : Matrix (Module.Free.ChooseBasisIndex K V) (Module.Free.ChooseBasisIndex K V) K :=
    LinearMap.toMatrix b b B
  obtain ⟨P, hP⟩ := WeilConjectures.exists_similar_to_transpose A
  let eFun : V ≃ₗ[K] Module.Free.ChooseBasisIndex K V → K := b.equivFun
  -- e = eFun⁻¹ ∘ P ∘ eFun : V ≃ V
  let e : V ≃ₗ[K] V := eFun.trans (P.trans eFun.symm)
  refine ⟨e.trans b.toDualEquiv, ?_⟩
  -- `toMatrix = toMatrix' ∘ eFun.conj`, so `eFun.conj B = toLin' A`
  have h_eFun : eFun.conj B = Matrix.toLin' A := by
    have hdef : LinearMap.toMatrix b b B = LinearMap.toMatrix' (eFun.conj B) := by
      dsimp only [LinearMap.toMatrix, LinearEquiv.trans_apply]
      rfl
    calc eFun.conj B
        = Matrix.toLin' (LinearMap.toMatrix' (eFun.conj B)) := by
            rw [Matrix.toLin'_toMatrix']
      _ = Matrix.toLin' (LinearMap.toMatrix b b B) := by rw [← hdef]
      _ = Matrix.toLin' A := rfl
  -- `e.conj B = toLin b b A.transpose`
  have h_e : e.conj B = Matrix.toLin b b A.transpose := by
    have hcomp : e.conj B = eFun.symm.conj (P.conj (eFun.conj B)) := by
      ext x
      simp [e, LinearEquiv.conj_apply, LinearEquiv.trans_apply]
    have h_toLin :
        Matrix.toLin b b A.transpose = eFun.symm.conj (Matrix.toLin' A.transpose) := by
      dsimp only [Matrix.toLin, LinearMap.toMatrix]
      -- `(arrowCongr eFun eFun).trans toMatrix').symm = toLin' then arrowCongr.symm
      -- and `arrowCongr eFun.symm eFun.symm = eFun.symm.conj`
      change
          (LinearEquiv.trans (LinearEquiv.arrowCongr eFun eFun) LinearMap.toMatrix').symm
            A.transpose =
          eFun.symm.conj (Matrix.toLin' A.transpose)
      rw [LinearEquiv.symm_trans_apply]
      -- toMatrix'.symm A.transpose = toLin' A.transpose
      change LinearEquiv.arrowCongr eFun.symm eFun.symm (Matrix.toLin' A.transpose) =
        eFun.symm.conj (Matrix.toLin' A.transpose)
      rfl
    calc e.conj B
        = eFun.symm.conj (P.conj (eFun.conj B)) := hcomp
      _ = eFun.symm.conj (P.conj (Matrix.toLin' A)) := by rw [h_eFun]
      _ = eFun.symm.conj (Matrix.toLin' A.transpose) := by rw [hP]
      _ = Matrix.toLin b b A.transpose := h_toLin.symm
  -- `toDualEquiv.conj (toLin b b Aᵀ) = B.dualMap` via equal matrices on dualBasis
  have h_dual : b.toDualEquiv.conj (Matrix.toLin b b A.transpose) = B.dualMap := by
    apply (LinearMap.toMatrix b.dualBasis b.dualBasis).injective
    have hgen (e₀ : V ≃ₗ[K] Module.Dual K V) (f : V →ₗ[K] V) :
        LinearMap.toMatrix (b.map e₀) (b.map e₀) (e₀.conj f) =
          LinearMap.toMatrix b b f := by
      ext i j
      simp [LinearMap.toMatrix_apply, LinearEquiv.conj_apply, Basis.map_apply, Basis.map_repr]
    have hL :
        LinearMap.toMatrix b.dualBasis b.dualBasis
            (b.toDualEquiv.conj (Matrix.toLin b b A.transpose)) =
          A.transpose := by
      simpa [Basis.dualBasis, LinearMap.toMatrix_toLin] using
        hgen b.toDualEquiv (Matrix.toLin b b A.transpose)
    have hR :
        LinearMap.toMatrix b.dualBasis b.dualBasis B.dualMap = A.transpose := by
      simp [LinearMap.dualMap_def, A, LinearMap.toMatrix_transpose]
    rw [hL, hR]
  have hcomp :
      (e.trans b.toDualEquiv).conj B = b.toDualEquiv.conj (e.conj B) := by
    ext x
    simp [LinearEquiv.conj_apply, LinearEquiv.trans_apply]
  calc (e.trans b.toDualEquiv).conj B
      = b.toDualEquiv.conj (e.conj B) := hcomp
    _ = b.toDualEquiv.conj (Matrix.toLin b b A.transpose) := by rw [h_e]
    _ = B.dualMap := h_dual
