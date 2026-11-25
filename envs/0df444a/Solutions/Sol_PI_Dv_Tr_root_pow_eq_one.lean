-- Prove2me | solution 1 for PI.Dv.Tr.root_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:48.229734+00:00
-- url     : https://prove2.me/submissions/e3bb69fc-5a54-459c-a718-77c51a38a21e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Module
namespace PI.Dv.Tr
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (m : ℕ) (hB : B ^ m = 1) (μ : ℂ)
    (hμ : μ ∈ B.charpoly.roots) : μ ^ m = 1 := by
  have hroot : B.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic B).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hsc : Matrix.mulVec (Matrix.scalar n μ) v = μ • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBv : Matrix.mulVec B v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
    exact hv.symm
  have hpow : ∀ k : ℕ, Matrix.mulVec (B ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 := hpow m
  rw [hB, Matrix.one_mulVec] at h1
  by_contra hne
  have h2 : (1 - μ ^ m) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact hne (by linear_combination -h)
  · exact hv0 h
end PI.Dv.Tr
