-- Prove2me | solution 1 for YuanDGD.Sublinear.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:15:46.816801+00:00
-- url     : https://prove2.me/submissions/60d59209-dc00-4b2c-84aa-cf83b3327a2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting
import Theorems.Thm_YuanDGD_Sublinear_lemma_1

set_option autoImplicit false

open YuanDGD.Linear YuanDGD.Sublinear Matrix

theorem solution {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ)
    (hn : 2 ≤ n) (hsymm : Wᵀ = W) (hds : W ∈ doublyStochastic ℝ (Fin n)) (hβ : beta W < 1)
    (hLf : ∀ i, 0 < Lf i)
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ Lf i * ‖a - b‖)
    (α : ℝ) (hα : 0 < α) (B : ℝ) (hB : ∀ s : ℕ, ‖hvec f (dgd W f α) s‖ ≤ B) :
    (∀ (k : ℕ) (i : Fin n),
      ‖gradient (f i) (dgd W f α k i) - gradient (f i) (xbar (dgd W f α) k)‖
        ≤ α * B * Lf i / (1 - beta W)) ∧
    ∀ k : ℕ, ‖gk f (dgd W f α) k - gbar f (dgd W f α) k‖ ≤ α * B * Lh Lf / (1 - beta W) := by
  have hL1 := YuanDGD.Sublinear.lemma_1 W f hn hsymm hds hβ α hα B hB
  have h1β : 0 < 1 - beta W := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have part1 : ∀ (k : ℕ) (i : Fin n),
      ‖gradient (f i) (dgd W f α k i) - gradient (f i) (xbar (dgd W f α) k)‖
        ≤ α * B * Lf i / (1 - beta W) := by
    intro k i
    calc ‖gradient (f i) (dgd W f α k i) - gradient (f i) (xbar (dgd W f α) k)‖
        ≤ Lf i * ‖dgd W f α k i - xbar (dgd W f α) k‖ := hlip i _ _
      _ ≤ Lf i * (α * B / (1 - beta W)) :=
          mul_le_mul_of_nonneg_left (hL1 k i) (hLf i).le
      _ = α * B * Lf i / (1 - beta W) := by ring
  refine ⟨part1, fun k => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLh : ∀ i, Lf i ≤ Lh Lf := fun i => le_ciSup (Finite.bddAbove_range Lf) i
  have hdiff : gk f (dgd W f α) k - gbar f (dgd W f α) k =
      (1 / (n : ℝ)) • ∑ i, (gradient (f i) (dgd W f α k i) -
        gradient (f i) (xbar (dgd W f α) k)) := by
    unfold gk gbar
    rw [← smul_sub, Finset.sum_sub_distrib]
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum : ‖∑ i, (gradient (f i) (dgd W f α k i) - gradient (f i) (xbar (dgd W f α) k))‖ ≤
      ∑ _i : Fin n, α * B * Lh Lf / (1 - beta W) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (part1 k i).trans ?_)
    apply div_le_div_of_nonneg_right _ h1β.le
    exact mul_le_mul_of_nonneg_left (hLh i) (mul_nonneg hα.le hB0)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc 1 / (n : ℝ) * ‖∑ i, (gradient (f i) (dgd W f α k i) -
        gradient (f i) (xbar (dgd W f α) k))‖
      ≤ 1 / (n : ℝ) * ((n : ℝ) * (α * B * Lh Lf / (1 - beta W))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = α * B * Lh Lf / (1 - beta W) := by field_simp
