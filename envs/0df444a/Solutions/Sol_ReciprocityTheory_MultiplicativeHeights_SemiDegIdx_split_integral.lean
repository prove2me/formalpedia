-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.split_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:39:23.145015+00:00
-- url     : https://prove2.me/submissions/b9aca046-3d37-4ebe-af1c-8042293e172b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_det_rowMat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_rows
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_smul_mem_of_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_smul_smul
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
    (hin : ∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) (hint : IsIntegralOn S X)
    (s t : Fin k → K) (hs : ∀ i, S.c (s i) ∈ C i) (ht : ∀ i, t i ∈ C i) :
    (∏ i, s i) * S.G.det * (∏ i, t i) ∈ (1 : Submodule (𝓞 K) K) := by
  let M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j => S.h (S.c (s i) • z i) (t j • z j)
  have hM : M = Matrix.diagonal s * (((rowMat z).map S.c * S.G) * (rowMat z)ᵀ) *
      Matrix.diagonal t := by
    ext i j
    simp only [M, Matrix.of_apply, hermForm_smul_smul, S.c_invol, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [hermForm_rows]
    simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]
    ring
  have hdet : M.det = (∏ i, s i) * S.G.det * (∏ i, t i) := by
    have : ((rowMat z).map S.c).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_rowMat z htri hdiag, map_one]
    rw [hM]
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
      det_rowMat z htri hdiag, this]
    ring
  have hent : ∀ i j, ∃ m : 𝓞 K, algebraMap (𝓞 K) K m = M i j := fun i j =>
    hint _ (smul_mem_of_split hin i (hs i)) _ (smul_mem_of_split hin j (ht j))
  choose m hm using hent
  have : M = (Matrix.of m).map (algebraMap (𝓞 K) K) := by
    ext i j
    simp [hm]
  rw [← hdet, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
