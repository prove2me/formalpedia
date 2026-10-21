-- Prove2me | solution 1 for ShortTermism.Commitment.eq_A_26
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:55:18.501991+00:00
-- url     : https://prove2.me/submissions/3aa5bb31-6cb0-4a2f-974b-52eb0586ae86

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model
import Theorems.Thm_ShortTermism_Commitment_hamiltonian_condensed
import Theorems.Thm_ShortTermism_Commitment_eu_argmax_section

open ShortTermism.Commitment

theorem solution (P : Params) (hP : P.Standing) (fu au eu : ℝ → ℝ)
    (hv : IsUnleveredValue P fu) (hu : IsUnleveredPolicy P fu au eu)
    (C : ℝ) (f : ℝ → ℝ) (δ : ℝ) (hδ : P.dlow ≤ δ) :
    IsGreatest
      ((fun e => hjbIntegrand P C δ (au δ) e (deriv f δ) (deriv (deriv f) δ)) '' Set.Icc 0 P.ebar)
      (hjbIntegrand P C δ (au δ) (eu δ) (deriv f δ) (deriv (deriv f) δ)) := by
  have hδpos : 0 < δ := lt_of_lt_of_le hP.2.2.2.2.2.2.2.2.2.2.2 hδ
  obtain ⟨hmem, hmax⟩ := eu_argmax_section P hP fu au eu hv hu δ hδ (deriv f δ)
  refine ⟨⟨eu δ, hmem, rfl⟩, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have h := hmax e he
  simp only
  rw [hamiltonian_condensed P hP, hamiltonian_condensed P hP]
  nlinarith [mul_le_mul_of_nonneg_left h hδpos.le]
