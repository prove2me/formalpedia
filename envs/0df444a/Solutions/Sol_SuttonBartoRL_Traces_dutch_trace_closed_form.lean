-- Prove2me | solution 1 for SuttonBartoRL.Traces.dutch_trace_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:57:56.253982+00:00
-- url     : https://prove2.me/submissions/10946035-2b46-418b-b681-a3dab0c3c802

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

set_option autoImplicit false

open SuttonBartoRL.Traces Matrix in
lemma dtcf_fade_succ {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (k t : ℕ) (hk : k ≤ t) :
    fadeProd α x (k + 1) (t + 1) = fadingMatrix α x (t + 1) * fadeProd α x (k + 1) t := by
  rw [fadeProd, if_pos (by omega)]

open SuttonBartoRL.Traces Matrix in
lemma dtcf_fade_self {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    fadeProd α x (t + 2) (t + 1) = 1 := by
  rw [fadeProd, if_neg (by omega)]

open SuttonBartoRL.Traces Matrix in
lemma dtcf_fading_mulVec {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (s : ℕ) (z : Fin d → ℝ) :
    fadingMatrix α x s *ᵥ z = z - (α * (z ⬝ᵥ x s)) • x s := by
  ext i
  simp only [fadingMatrix, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [vecMulVec_mulVec]
  simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm]
  ring

open SuttonBartoRL.Traces Matrix in
theorem solution {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    dutchTrace α x t = ∑ k ∈ Finset.range (t + 1), fadeProd α x (k + 1) t *ᵥ x k := by
  induction t with
  | zero =>
    simp [dutchTrace, fadeProd]
  | succ t ih =>
    rw [Finset.sum_range_succ, dtcf_fade_self, one_mulVec]
    have h : ∑ k ∈ Finset.range (t + 1), fadeProd α x (k + 1) (t + 1) *ᵥ x k
        = fadingMatrix α x (t + 1) *ᵥ ∑ k ∈ Finset.range (t + 1), fadeProd α x (k + 1) t *ᵥ x k := by
      rw [mulVec_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [dtcf_fade_succ α x k t (by simpa [Nat.lt_succ_iff] using hk), mulVec_mulVec]
    rw [h, ← ih, dtcf_fading_mulVec, dutchTrace]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
