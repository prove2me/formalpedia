-- Prove2me | solution 1 for PI.Dv.GLPTr.star_trace_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:35.745386+00:00
-- url     : https://prove2.me/submissions/d6af3b3d-728f-4e3b-bfee-91cdc3ab54c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_StarMapTraceOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLPTr
open Matrix
open scoped ComplexOrder
namespace PI.Dv.GLPTr
theorem _root_.solution {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) :
    star A.trace = (A ^ (n - 1)).trace := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set Q : Matrix d d ℂ := ∑ k ∈ Finset.range (m + 1), (A ^ k)ᴴ * A ^ k with hQdef
  have hQpd : Q.PosDef := by
    rw [hQdef, Finset.sum_range_succ']
    simp only [pow_zero, conjTranspose_one, one_mul]
    rw [add_comm]
    exact (PosDef.one).add_posSemidef
      (posSemidef_sum _ fun k _ => posSemidef_conjTranspose_mul_self _)
  have hAQ : Aᴴ * Q * A = Q := by
    rw [hQdef, Finset.mul_sum, Finset.sum_mul]
    have : ∀ k, Aᴴ * ((A ^ k)ᴴ * A ^ k) * A = (A ^ (k + 1))ᴴ * A ^ (k + 1) := by
      intro k
      rw [pow_succ, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp only [this]
    have key : ∀ F : ℕ → Matrix d d ℂ, F (m + 1) = F 0 →
        ∑ x ∈ Finset.range (m + 1), F (x + 1) = ∑ x ∈ Finset.range (m + 1), F x := by
      intro F hF
      rw [Finset.sum_range_succ, Finset.sum_range_succ' F, hF]
    exact key (fun k => (A ^ k)ᴴ * A ^ k) (by simp [hA])
  have hAQ' : Aᴴ * Q = Q * A ^ m := by
    have h2 : Aᴴ * Q * A * A ^ m = Q * A ^ m := by rw [hAQ]
    rw [Matrix.mul_assoc, ← pow_succ', hA, Matrix.mul_one] at h2
    exact h2
  have hU : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQpd.isUnit
  have hinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hU
  have hinv' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hU
  calc star A.trace = (Aᴴ).trace := (trace_conjTranspose A).symm
    _ = (Aᴴ * (Q * Q⁻¹)).trace := by rw [hinv, Matrix.mul_one]
    _ = (Q⁻¹ * (Aᴴ * Q)).trace := by rw [← Matrix.mul_assoc, trace_mul_comm]
    _ = (A ^ m).trace := by rw [hAQ', ← Matrix.mul_assoc, hinv', Matrix.one_mul]
end PI.Dv.GLPTr
