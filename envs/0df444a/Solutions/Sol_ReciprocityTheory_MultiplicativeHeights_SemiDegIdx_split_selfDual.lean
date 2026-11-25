-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:43.149356+00:00
-- url     : https://prove2.me/submissions/a9fd0595-b234-474d-b7ea-fcddec9c0232

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_smul_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_det_rowMat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_rows
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_integral_of_mem_one
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_det_mem_prod_sub
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_conj
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_sum_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_one_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    {X : Submodule (𝓞 K) (Fin k → K)} {C : Fin k → Submodule (𝓞 K) K} {z : Fin k → Fin k → K}
    (htri : ∀ j i : Fin k, i < j → z j i = 0) (hdiag : ∀ j, z j j = 1)
    (hdec : ∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i)
    (hsd : IsSelfDual S X) (hG : S.G.det ≠ 0) (u : Fin k → K)
    (hu : ∀ j, ∀ w, S.c w ∈ C j → u j * w ∈ (1 : Submodule (𝓞 K) K)) :
    ∏ j, u j ∈ Submodule.span (𝓞 K) {S.G.det} * ∏ i, C i := by
  classical
  set Q : Matrix (Fin k) (Fin k) K := (rowMat z).map S.c * S.G with hQ
  have hQdet : Q.det = S.G.det := by
    rw [hQ, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_rowMat z htri hdiag, map_one, one_mul]
  have hQu : IsUnit Q.det := by rw [hQdet]; exact isUnit_iff_ne_zero.2 hG
  let y : Fin k → Fin k → K := fun j => Q⁻¹ *ᵥ Pi.single j (u j)
  have hQy : ∀ j, Q *ᵥ y j = Pi.single j (u j) := fun j => by
    simp only [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mulVec]
  have hy : ∀ j, y j ∈ X := by
    intro j
    refine hsd.2 _ fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hdec x hx
    rw [← hermForm_conj]
    have : S.h (∑ i, t i • z i) (y j) = S.c (t j) * u j := by
      rw [hermForm_sum_left]
      simp only [hermForm_smul_left, hermForm_rows, ← hQ, hQy, Pi.single_apply]
      simp
    rw [this]
    refine integral_of_mem_one (mem_one_map S.c ?_)
    rw [mul_comm]
    exact hu j _ (by rw [S.c_invol]; exact ht j)
  choose T hT hTy using fun j => hdec (y j) (hy j)
  let Tm : Matrix (Fin k) (Fin k) K := Matrix.of fun i j => T j i
  have hY1 : (Matrix.of fun a j => y j a) = (rowMat z)ᵀ * Tm := by
    ext a j
    simp only [Matrix.of_apply]
    rw [hTy j]
    simp [Tm, rowMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  have hY2 : (Matrix.of fun a j => y j a) = Q⁻¹ * Matrix.diagonal u := by
    ext a j
    simp [y, Matrix.mul_diagonal, mul_comm]
  have hdet : (∏ j, u j) = S.G.det * Tm.det := by
    have h1 := congrArg Matrix.det hY1
    rw [hY2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_rowMat z htri hdiag,
      one_mul, Matrix.det_nonsing_inv, Matrix.det_diagonal, hQdet, Ring.inverse_eq_inv'] at h1
    rw [← h1]
    field_simp
  rw [hdet]
  exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _)
    (det_mem_prod_sub C Tm fun i j => hT j i)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
