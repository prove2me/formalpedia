-- Prove2me | solution 1 for PI.Dv.TIW.root_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:57.886331+00:00
-- url     : https://prove2.me/submissions/c33ce59e-2ca9-4db4-8cf9-e5a5e7d84ef4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Matrix
namespace PI.Dv.TIW
theorem _root_.solution {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hM : M ^ m = 1)
    (μ : ℂ) (hμ : μ ∈ M.charpoly.roots) : μ ^ m = 1 := by
  have hroot : M.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hMv : M *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, funext_iff, Pi.smul_apply, smul_eq_mul]
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have := hpow m
  rw [hM, Matrix.one_mulVec] at this
  have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0
end PI.Dv.TIW
