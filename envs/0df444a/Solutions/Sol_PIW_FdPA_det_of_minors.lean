-- Prove2me | solution 1 for PIW.FdPA.det_of_minors
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:12:57.540221+00:00
-- url     : https://prove2.me/submissions/e31870f9-77b9-48b1-80dd-bf4848ceaac5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section

theorem PIW.FdPA.det_of_minors {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (τ : X.Ψ) (h : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re) :
    (mat x τ).det ≠ 0 := by
  intro hdet
  have hr := h (Fin.last r)
  have hg : gram τ.1 X.Gm (mat x τ) =
      (mat x τ).transpose * (X.Gm.map τ.1) * (mat x τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsub : (gram τ.1 X.Gm (mat x τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt))
      (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt)) = gram τ.1 X.Gm (mat x τ) := by
    ext a b; rfl
  have h0 : dmin X.Gm x τ (Fin.last r) = 0 := by
    unfold dmin lminor
    rw [hsub, hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet]
    simp
  rw [h0] at hr
  simp at hr

theorem solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (τ : X.Ψ) (h : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re) :
    (mat x τ).det ≠ 0 := by
  intro hdet
  have hr := h (Fin.last r)
  have hg : gram τ.1 X.Gm (mat x τ) =
      (mat x τ).transpose * (X.Gm.map τ.1) * (mat x τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsub : (gram τ.1 X.Gm (mat x τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt))
      (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt)) = gram τ.1 X.Gm (mat x τ) := by
    ext a b; rfl
  have h0 : dmin X.Gm x τ (Fin.last r) = 0 := by
    unfold dmin lminor
    rw [hsub, hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet]
    simp
  rw [h0] at hr
  simp at hr
