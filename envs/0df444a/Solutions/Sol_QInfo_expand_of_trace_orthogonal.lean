-- Prove2me | solution 1 for QInfo.expand_of_trace_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:31:35.504662+00:00
-- url     : https://prove2.me/submissions/673b3180-47a7-4498-a9b2-1cf02bb5e6c3

import Mathlib

open Matrix
open scoped ComplexOrder

theorem solution {X κ : Type*} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (σ : κ → Matrix X X ℂ)
    (horth : ∀ a b, (σ a * σ b).trace = if a = b then (Fintype.card X : ℂ) else 0)
    (hcard : Fintype.card κ = Fintype.card X ^ 2) (M : Matrix X X ℂ) :
    M = (Fintype.card X : ℂ)⁻¹ • ∑ a, (σ a * M).trace • σ a := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Subsingleton.elim _ _
  have hd : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hli : LinearIndependent ℂ σ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg b
    have := congrArg (fun N => (N * σ b).trace) hg
    simp only [Finset.sum_mul, trace_sum, Matrix.smul_mul, trace_smul, smul_eq_mul, horth,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.zero_mul,
      trace_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hd
  have hne : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hcard]; exact pow_pos Fintype.card_pos 2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by
    rw [hcard, Module.finrank_matrix, Module.finrank_self, mul_one, sq])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (hspan ▸ Submodule.mem_top : M ∈ Submodule.span ℂ (Set.range σ))
  have hcoef : ∀ b, (σ b * M).trace = c b * Fintype.card X := by
    intro b
    rw [← hc, Finset.mul_sum, trace_sum]
    simp only [Matrix.mul_smul, trace_smul, smul_eq_mul, horth, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => rw [← hc]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hcoef, smul_smul, mul_comm (c b), ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

