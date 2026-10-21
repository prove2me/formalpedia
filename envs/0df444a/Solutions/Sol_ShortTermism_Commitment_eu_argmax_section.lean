-- Prove2me | solution 1 for ShortTermism.Commitment.eu_argmax_section
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:53:26.779988+00:00
-- url     : https://prove2.me/submissions/ea586543-1383-4dbe-857a-7af2d593a91f

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model
import Theorems.Thm_ShortTermism_Commitment_hamiltonian_condensed

open ShortTermism.Commitment

theorem solution (P : Params) (hP : P.Standing) (fu au eu : ℝ → ℝ)
    (hv : IsUnleveredValue P fu) (hu : IsUnleveredPolicy P fu au eu)
    (δ : ℝ) (hδ : P.dlow ≤ δ) (f1 : ℝ) :
    eu δ ∈ Set.Icc 0 P.ebar ∧
      ∀ e ∈ Set.Icc 0 P.ebar, condensedObj P δ (au δ) e f1 ≤ condensedObj P δ (au δ) (eu δ) f1 := by
  obtain ⟨hmem, hmax⟩ := hu δ hδ
  have hδpos : 0 < δ := lt_of_lt_of_le hP.2.2.2.2.2.2.2.2.2.2.2 hδ
  refine ⟨hmem.2, fun e he => ?_⟩
  have h := hmax (au δ, e) ⟨hmem.1, he⟩
  simp only at h
  rw [hamiltonian_condensed P hP, hamiltonian_condensed P hP] at h
  -- the f1-dependence of condensedObj cancels in the difference
  have key : condensedObj P δ (au δ) e f1 - condensedObj P δ (au δ) (eu δ) f1
      = condensedObj P δ (au δ) e (deriv fu δ) - condensedObj P δ (au δ) (eu δ) (deriv fu δ) := by
    unfold condensedObj; ring
  have h2 : δ * (condensedObj P δ (au δ) e (deriv fu δ)
      - condensedObj P δ (au δ) (eu δ) (deriv fu δ)) ≤ 0 := by nlinarith
  have h3 : condensedObj P δ (au δ) e (deriv fu δ)
      - condensedObj P δ (au δ) (eu δ) (deriv fu δ) ≤ 0 := by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hδpos hc]
  linarith
