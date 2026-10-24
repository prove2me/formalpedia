-- Prove2me | solution 1 for SKAlgorithm.Qudit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:23:04.700986+00:00
-- url     : https://prove2.me/submissions/7f8a2315-c364-49df-a9f3-edd3b3a9d84a

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix Matrix.Norms.L2Operator
open QAlgorithms

namespace SKAlgorithm.Qudit.PerturbationProof

variable {d : ℕ}
variable {U Ut V W Vt Wt : Matrix (Fin d) (Fin d) ℂ}

lemma norm_conj_sub_conj_le
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hUt : Ut ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖U * X * star U - Ut * X * star Ut‖ ≤ 2 * ‖U - Ut‖ * ‖X‖ := by
  have heq : U * X * star U - Ut * X * star Ut =
      (U - Ut) * X * star U + Ut * (X * (star U - star Ut)) := by
    noncomm_ring
  rw [heq]
  calc
    ‖(U - Ut) * X * star U + Ut * (X * (star U - star Ut))‖ ≤
        ‖(U - Ut) * X * star U‖ + ‖Ut * (X * (star U - star Ut))‖ := norm_add_le _ _
    _ = ‖(U - Ut) * X‖ + ‖X * (star U - star Ut)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU),
        CStarRing.norm_mem_unitary_mul _ hUt]
    _ ≤ ‖U - Ut‖ * ‖X‖ + ‖X‖ * ‖star U - star Ut‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖U - Ut‖ * ‖X‖ := by rw [← star_sub, norm_star]; ring

lemma norm_commutator_change_left_le
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hVt : Vt ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ‖V * W * star V * star W - Vt * W * star Vt * star W‖ ≤
      2 * ‖V - Vt‖ * ‖W - 1‖ := by
  have heq : V * W * star V - Vt * W * star Vt =
      V * (W - 1) * star V - Vt * (W - 1) * star Vt := by
    simp only [mul_sub, sub_mul, mul_one, Unitary.mul_star_self_of_mem hV,
      Unitary.mul_star_self_of_mem hVt]
    noncomm_ring
  rw [← sub_mul, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hW), heq]
  exact norm_conj_sub_conj_le hV hVt (W - 1)

lemma norm_commutator_change_right_le
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hWt : Wt ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ‖V * W * star V * star W - V * Wt * star V * star Wt‖ ≤
      2 * ‖W - Wt‖ * ‖V - 1‖ := by
  have heq : V * W * star V * star W - V * Wt * star V * star Wt =
      V * (W * (star V - 1) * star W - Wt * (star V - 1) * star Wt) := by
    simp only [mul_sub, sub_mul, mul_one, Unitary.mul_star_self_of_mem hW,
      Unitary.mul_star_self_of_mem hWt]
    noncomm_ring
  rw [heq, CStarRing.norm_mem_unitary_mul _ hV]
  convert norm_conj_sub_conj_le hW hWt (star V - 1) using 1
  rw [show ‖star V - 1‖ = ‖V - 1‖ from by
    simpa only [star_sub, star_one] using norm_star (V - 1)]

end SKAlgorithm.Qudit.PerturbationProof

theorem solution {d : ℕ} (V W Vt Wt : Matrix (Fin d) (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hVt : Vt ∈ Matrix.unitaryGroup (Fin d) ℂ) (hWt : Wt ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (Δ δ : ℝ) (hVVt : specNorm (V - Vt) < Δ) (hWWt : specNorm (W - Wt) < Δ)
    (hIV : specNorm (1 - V) < δ) (hIW : specNorm (1 - W) < δ) :
    specNorm (V * W * Vᴴ * Wᴴ - Vt * Wt * Vtᴴ * Wtᴴ) <
      8 * Δ * δ + 4 * Δ * δ ^ 2 + 8 * Δ ^ 2 + 4 * Δ ^ 3 + Δ ^ 4 := by
  change ‖V - Vt‖ < Δ at hVVt
  change ‖W - Wt‖ < Δ at hWWt
  change ‖1 - V‖ < δ at hIV
  change ‖1 - W‖ < δ at hIW
  change ‖V * W * star V * star W - Vt * Wt * star Vt * star Wt‖ < _
  have hΔ : 0 < Δ := lt_of_le_of_lt (norm_nonneg _) hVVt
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hIV
  have hVt1 : ‖Vt - 1‖ ≤ δ + Δ := by
    calc
      ‖Vt - 1‖ ≤ ‖Vt - V‖ + ‖V - 1‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (Vt - V) (V - 1)
      _ ≤ Δ + δ := by
        rw [norm_sub_rev Vt V, norm_sub_rev V 1]
        exact add_le_add hVVt.le hIV.le
      _ = δ + Δ := add_comm _ _
  have hb : ‖V * W * star V * star W - Vt * Wt * star Vt * star Wt‖ ≤
      4 * Δ * δ + 2 * Δ ^ 2 := by
    calc
      ‖V * W * star V * star W - Vt * Wt * star Vt * star Wt‖ ≤
          ‖V * W * star V * star W - Vt * W * star Vt * star W‖ +
          ‖Vt * W * star Vt * star W - Vt * Wt * star Vt * star Wt‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (V * W * star V * star W - Vt * W * star Vt * star W)
            (Vt * W * star Vt * star W - Vt * Wt * star Vt * star Wt)
      _ ≤ 2 * ‖V - Vt‖ * ‖W - 1‖ + 2 * ‖W - Wt‖ * ‖Vt - 1‖ :=
        add_le_add
          (SKAlgorithm.Qudit.PerturbationProof.norm_commutator_change_left_le hV hVt hW)
          (SKAlgorithm.Qudit.PerturbationProof.norm_commutator_change_right_le hVt hW hWt)
      _ ≤ 2 * Δ * δ + 2 * Δ * (δ + Δ) := by
        apply add_le_add
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hVVt.le (by norm_num)
          · simpa only [norm_sub_rev] using hIW.le
          · exact norm_nonneg _
          · positivity
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hWWt.le (by norm_num)
          · exact hVt1
          · exact norm_nonneg _
          · positivity
      _ = 4 * Δ * δ + 2 * Δ ^ 2 := by ring
  have hstrict : 4 * Δ * δ + 2 * Δ ^ 2 < 8 * Δ * δ + 8 * Δ ^ 2 := by
    nlinarith [mul_pos hΔ hδ, sq_pos_of_pos hΔ]
  have hrest : 0 ≤ 4 * Δ * δ ^ 2 + 4 * Δ ^ 3 + Δ ^ 4 := by positivity
  linarith
