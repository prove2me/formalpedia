-- Prove2me | solution 1 for OffloadGNEP.Mono.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:55:36.300475+00:00
-- url     : https://prove2.me/submissions/c6f8a75a-a31b-4db4-a331-c8f870f9b671

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

set_option autoImplicit false
open OffloadGNEP.Mono

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (x : Fin N → Tier → ℝ) (hD : D P x ≠ 0) :
    Bs P x = (1 / ((P.n : ℝ) * D P x ^ 2)) •
      (Matrix.vecMulVec P.delta P.delta).hadamard
        (1 + Eall + (1 / ((P.n : ℝ) * D P x)) •
          (Matrix.vecMulVec (xdelta P x) ones + Matrix.vecMulVec ones (xdelta P x))) := by
  have hn : (P.n : ℝ) ≠ 0 := by
    have := hS.1
    exact_mod_cast this.ne'
  obtain ⟨Dv, hDv⟩ : ∃ Dv, Dv = D P x := ⟨_, rfl⟩
  rw [← hDv] at hD ⊢
  set S : ℝ := ∑ w, P.delta w * x w .clet with hSdef
  have hl : load P x = 1 - Dv := by
    rw [hDv]; unfold D; ring
  have hlS : load P x = 1 / (P.n : ℝ) * S := rfl
  have e1 : ∀ a : ℝ, 1 - 1 / (P.n : ℝ) * (S - a) = Dv + 1 / (P.n : ℝ) * a := by
    intro a
    have : 1 / (P.n : ℝ) * S = 1 - Dv := by rw [← hlS, hl]
    rw [mul_sub]; linarith
  ext u v
  simp only [Bs, Bmat, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.hadamard_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Eall, ones, xdelta, smul_eq_mul]
  by_cases h : u = v
  · subst h
    have hsum : ∑ w ∈ Finset.univ.erase u, P.delta w * x w .clet = S - P.delta u * x u .clet :=
      Finset.sum_erase_eq_sub (Finset.mem_univ u)
    simp only [Bu, if_true, hsum, e1, hl]
    field_simp
    have hi : Dv * Dv⁻¹ = 1 := mul_inv_cancel₀ hD
    linear_combination (P.delta u ^ 2 * Dv * ↑P.n + P.delta u ^ 3 * x u .clet) *
      ((Dv * Dv⁻¹) ^ 2 + Dv * Dv⁻¹ + 1) * hi
  · simp only [h, if_false, Ne.symm h, Buv, hl]
    field_simp
    have hi : Dv * Dv⁻¹ = 1 := mul_inv_cancel₀ hD
    linear_combination (P.delta u * P.delta v * Dv * ↑P.n * 2 + P.delta u * P.delta v ^ 2 * x v .clet * 2 +
      P.delta u ^ 2 * P.delta v * x u .clet * 2) * ((Dv * Dv⁻¹) ^ 2 + Dv * Dv⁻¹ + 1) * hi
