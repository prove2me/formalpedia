-- Prove2me | solution 1 for SKAlgorithm.Qudit.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:27:30.287457+00:00
-- url     : https://prove2.me/submissions/e4038b8b-1be0-45a6-a60a-d7b8bce0714b

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open QAlgorithms NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

/-! The local remainder and commutator estimates adapt the actual accepted proof of
QAlgorithms.Childs.su2_small_commutator_factorization (submission
de0f1e97-d1de-4bb6-909b-7d68a2561cde) from Fin 2 to arbitrary nonempty Fin d.
All proofs are included here; no theorem from that development is imported. -/

namespace SKAlgorithm.Qudit.ExpCommutatorProof

variable {d : ℕ} [Nonempty (Fin d)]

lemma exp_remainder (X : Matrix (Fin d) (Fin d) ℂ) (hX : ‖X‖ ≤ 1) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 := by
  have hs := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) X)
  have ht := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    pow_zero, pow_one, one_smul] at hs ht
  have hb : ‖exp X - (1 + X)‖ ≤ exp ‖X‖ - (1 + ‖X‖) := by
    apply hs.norm_le_of_bounded ht
    intro n
    simp only [norm_smul, norm_inv, Real.norm_natCast, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le X (n + 2)) (by positivity)
  have hr := Real.norm_exp_sub_one_sub_id_le (x := ‖X‖) (by simpa using hX)
  rw [Real.exp_eq_exp_ℝ] at hr
  calc
    _ = ‖exp X - (1 + X)‖ := by congr 1; abel
    _ ≤ exp ‖X‖ - (1 + ‖X‖) := hb
    _ ≤ ‖exp ‖X‖ - 1 - ‖X‖‖ := by
      simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub] using
        (le_abs_self (exp ‖X‖ - 1 - ‖X‖))
    _ ≤ ‖X‖ ^ 2 := by simpa using hr

lemma exp_distance (X : Matrix (Fin d) (Fin d) ℂ) (hX : ‖X‖ ≤ 1) :
    ‖exp X - 1‖ ≤ ‖X‖ + ‖X‖ ^ 2 := by
  calc
    _ = ‖X + (exp X - 1 - X)‖ := by congr 1; abel
    _ ≤ ‖X‖ + ‖exp X - 1 - X‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (exp_remainder X hX)

omit [Nonempty (Fin d)] in
lemma bracket_bound (X Y : Matrix (Fin d) (Fin d) ℂ) :
    ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc
    _ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

lemma exp_commutator_error (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (X Y : Matrix (Fin d) (Fin d) ℂ) (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r)
    (hU : exp X ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hV : exp Y ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ‖exp (X * Y - Y * X) - exp X * exp Y * star (exp X) * star (exp Y)‖ ≤
      18 * r ^ 3 := by
  let U := exp X
  let V := exp Y
  let E := U - 1 - X
  let F := V - 1 - Y
  let W := X * Y - Y * X
  have hrle : r ≤ 1 := by linarith
  have he : ‖E‖ ≤ r ^ 2 := (exp_remainder X (hX.trans hrle)).trans (by gcongr)
  have hf : ‖F‖ ≤ r ^ 2 := (exp_remainder Y (hY.trans hrle)).trans (by gcongr)
  have hu : ‖U - 1‖ ≤ 2 * r := by
    calc
      _ ≤ ‖X‖ + ‖X‖ ^ 2 := exp_distance X (hX.trans hrle)
      _ ≤ r + r ^ 2 := by gcongr
      _ ≤ 2 * r := by nlinarith
  have hv : ‖V - 1‖ ≤ 2 * r := by
    calc
      _ ≤ ‖Y‖ + ‖Y‖ ^ 2 := exp_distance Y (hY.trans hrle)
      _ ≤ r + r ^ 2 := by gcongr
      _ ≤ 2 * r := by nlinarith
  have hw : ‖W‖ ≤ 2 * r ^ 2 := by
    calc
      _ ≤ 2 * ‖X‖ * ‖Y‖ := bracket_bound X Y
      _ ≤ 2 * r * r := by gcongr
      _ = _ := by ring
  have hr4 : r ^ 4 ≤ r ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hr 3) (sub_nonneg.mpr hrle)]
  have hd : ‖U * V - V * U - W‖ ≤ 6 * r ^ 3 := by
    have hid : U * V - V * U - W =
        (X * F - F * X) + (E * Y - Y * E) + (E * F - F * E) := by
      dsimp [E, F, W]
      noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖X * F - F * X‖ + ‖E * Y - Y * E‖ + ‖E * F - F * E‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 * ‖X‖ * ‖F‖ + 2 * ‖E‖ * ‖Y‖ + 2 * ‖E‖ * ‖F‖ := by
        exact add_le_add (add_le_add (bracket_bound X F) (bracket_bound E Y)) (bracket_bound E F)
      _ ≤ 2 * r * r ^ 2 + 2 * r ^ 2 * r + 2 * r ^ 2 * r ^ 2 := by gcongr
      _ ≤ 6 * r ^ 3 := by nlinarith
  have hs : ‖star U * star V - 1‖ ≤ 4 * r := by
    calc
      _ = ‖star U * (star V - 1) + (star U - 1)‖ := by congr 1; noncomm_ring
      _ ≤ ‖star U * (star V - 1)‖ + ‖star U - 1‖ := norm_add_le _ _
      _ = ‖V - 1‖ + ‖U - 1‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hU)]
        rw [show star V - 1 = star (V - 1) by simp,
          show star U - 1 = star (U - 1) by simp, norm_star, norm_star]
      _ ≤ 4 * r := by linarith
  have hc : ‖U * V * star U * star V - 1 - W‖ ≤ 14 * r ^ 3 := by
    have hid : U * V * star U * star V - 1 - W =
        (U * V - V * U - W) * star U * star V + W * (star U * star V - 1) := by
      have hvu : V * U * star U * star V = 1 := by
        rw [mul_assoc V U (star U), hU.2, mul_one, hV.2]
      calc
        _ = U * V * star U * star V - V * U * star U * star V - W := by rw [hvu]
        _ = _ := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖(U * V - V * U - W) * star U * star V‖ + ‖W * (star U * star V - 1)‖ := norm_add_le _ _
      _ = ‖U * V - V * U - W‖ + ‖W * (star U * star V - 1)‖ := by
        rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hV),
          CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU)]
      _ ≤ 6 * r ^ 3 + (2 * r ^ 2) * (4 * r) := by
        exact add_le_add hd ((norm_mul_le _ _).trans (mul_le_mul hw hs (norm_nonneg _) (by positivity)))
      _ = 14 * r ^ 3 := by ring
  have hew : ‖exp W - 1 - W‖ ≤ 4 * r ^ 3 := by
    calc
      _ ≤ ‖W‖ ^ 2 := exp_remainder W (hw.trans (by nlinarith))
      _ ≤ (2 * r ^ 2) ^ 2 := by gcongr
      _ ≤ 4 * r ^ 3 := by nlinarith
  calc
    _ = ‖(exp W - 1 - W) - (U * V * star U * star V - 1 - W)‖ := by
      dsimp [W, U, V]
      congr 1
      abel
    _ ≤ ‖exp W - 1 - W‖ + ‖U * V * star U * star V - 1 - W‖ := norm_sub_le _ _
    _ ≤ 4 * r ^ 3 + 14 * r ^ 3 := add_le_add hew hc
    _ = _ := by ring


end SKAlgorithm.Qudit.ExpCommutatorProof

open SKAlgorithm.Qudit.ExpCommutatorProof

theorem solution :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (d : ℕ) (F G : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ),
        F.IsHermitian → G.IsHermitian →
        specNorm F < δ → specNorm G < δ →
        specNorm
          (NormedSpace.exp (Complex.I • F) *
           NormedSpace.exp (Complex.I • G) *
           NormedSpace.exp ((-Complex.I) • F) *
           NormedSpace.exp ((-Complex.I) • G) -
           NormedSpace.exp (Complex.I • (Complex.I • (F * G - G * F)))) ≤
          c₁ * δ ^ 3 := by
  refine ⟨18, by norm_num, ?_⟩
  intro d F G δ hF hG hFn hGn
  change ‖F‖ < δ at hFn
  change ‖G‖ < δ at hGn
  change ‖_‖ ≤ _
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg F) hFn
  by_cases hd : d = 0
  · subst d
    have hz :
        exp (Complex.I • F) * exp (Complex.I • G) * exp ((-Complex.I) • F) *
          exp ((-Complex.I) • G) - exp (Complex.I • (Complex.I • (F * G - G * F))) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := .restrictScalars ℚ ℂ _
  let X := Complex.I • F
  let Y := Complex.I • G
  have hX : ‖X‖ ≤ δ := by simpa [X, norm_smul] using hFn.le
  have hY : ‖Y‖ ≤ δ := by simpa [Y, norm_smul] using hGn.le
  have hXs : X ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    hF.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I
  have hYs : Y ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    hG.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I
  have hU := exp_mem_unitary_of_mem_skewAdjoint hXs
  have hV := exp_mem_unitary_of_mem_skewAdjoint hYs
  have hstarX : star (exp X) = exp ((-Complex.I) • F) := by
    rw [star_exp, skewAdjoint.mem_iff.mp hXs]
    simp [X]
  have hstarY : star (exp Y) = exp ((-Complex.I) • G) := by
    rw [star_exp, skewAdjoint.mem_iff.mp hYs]
    simp [Y]
  have hbracket : X * Y - Y * X = Complex.I • (Complex.I • (F * G - G * F)) := by
    simp [X, Y, smul_smul, smul_sub]
  have hWs : X * Y - Y * X ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp [star_sub, star_mul, skewAdjoint.mem_iff.mp hXs, skewAdjoint.mem_iff.mp hYs]
  have hW := exp_mem_unitary_of_mem_skewAdjoint hWs
  rw [← hbracket, ← hstarX, ← hstarY]
  change ‖exp X * exp Y * star (exp X) * star (exp Y) - exp (X * Y - Y * X)‖ ≤ _
  by_cases hsmall : δ ≤ 1 / 2
  · rw [norm_sub_rev]
    exact exp_commutator_error δ hδ.le hsmall X Y hX hY hU hV
  · have hprod : exp X * exp Y * star (exp X) * star (exp Y) ∈
        unitary (Matrix (Fin d) (Fin d) ℂ) :=
      mul_mem (mul_mem (mul_mem hU hV) (Unitary.star_mem hU)) (Unitary.star_mem hV)
    calc
      _ ≤ ‖exp X * exp Y * star (exp X) * star (exp Y)‖ + ‖exp (X * Y - Y * X)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [CStarRing.norm_of_mem_unitary hprod, CStarRing.norm_of_mem_unitary hW]; norm_num
      _ ≤ 18 * δ ^ 3 := by
        have hhalf : 1 / 2 ≤ δ := le_of_lt (lt_of_not_ge hsmall)
        nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf,
          mul_nonneg (sub_nonneg.mpr hhalf) (sq_nonneg δ)]
