-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.KAKA.gram_diag_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:44:27.326316+00:00
-- url     : https://prove2.me/submissions/1a5076cc-de73-43bc-af9f-1c1ac4b586ac

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_GramDiagUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.KAKA
open Matrix
namespace PositivityTheory.Rg.Sw.KAKA
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℝ)
    (hM : Mᴴ * M = diagonal (fun j => ((s j ^ 2 : ℝ) : ℂ))) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ M = U * diagonal (fun j => (s j : ℂ)) := by
  classical
  let c : Fin n → EuclideanSpace ℂ (Fin n) := fun j => WithLp.toLp 2 (fun i => M i j)
  have hin : ∀ j k, inner ℂ (c j) (c k) = (Mᴴ * M) j k := by
    intro j k
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun j => ((s j : ℂ)⁻¹) • c j
  let S : Set (Fin n) := {j | s j ≠ 0}
  have hv : Orthonormal ℂ (S.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨k, hk⟩
    change inner ℂ (v j) (v k) = _
    simp only [v, inner_smul_left, inner_smul_right, hin, hM, Matrix.diagonal_apply]
    by_cases hjk : j = k
    · subst hjk
      have hj' : (s j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp only [if_true]
      rw [Complex.ofReal_pow, map_inv₀, Complex.conj_ofReal]
      field_simp
    · have : (⟨j, hj⟩ : S) ≠ ⟨k, hk⟩ := fun h => hjk (congrArg Subtype.val h)
      simp [hjk]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hU := (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  set U := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b with hUd
  refine ⟨U, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  · have hUe : ∀ i j, U i j = (b j).ofLp i := by
      intro i j
      simp [hUd, Module.Basis.toMatrix_apply]
    ext i j
    rw [Matrix.mul_diagonal, hUe]
    by_cases hj : s j = 0
    · have hc : c j = 0 := by
        have h1 := hin j j
        rw [hM, Matrix.diagonal_apply_eq, hj] at h1
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero] at h1
        exact inner_self_eq_zero.mp h1
      have : M i j = 0 := by
        have := congrArg (fun x : EuclideanSpace ℂ (Fin n) => x.ofLp i) hc
        simpa [c] using this
      rw [this, hj]; simp
    · have hbj : b j = v j := hb j hj
      rw [hbj]
      have hj' : (s j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp only [v, c, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      field_simp
end PositivityTheory.Rg.Sw.KAKA
