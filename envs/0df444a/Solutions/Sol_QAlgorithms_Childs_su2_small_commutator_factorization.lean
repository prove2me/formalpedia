-- Prove2me | solution 1 for QAlgorithms.Childs.su2_small_commutator_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:07:58.508643+00:00
-- url     : https://prove2.me/submissions/de0f1e97-d1de-4bb6-909b-7d68a2561cde

import Theorems.Thm_QAlgorithms_Childs_su2_balanced_lie_bracket

open QAlgorithms NormedSpace
open scoped Matrix.Norms.L2Operator

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev SU := Matrix.specialUnitaryGroup (Fin 2) ℂ

private lemma exp_remainder (X : Mat) (hX : ‖X‖ ≤ 1) :
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

private lemma exp_distance (X : Mat) (hX : ‖X‖ ≤ 1) :
    ‖exp X - 1‖ ≤ ‖X‖ + ‖X‖ ^ 2 := by
  calc
    _ = ‖X + (exp X - 1 - X)‖ := by congr 1; abel
    _ ≤ ‖X‖ + ‖exp X - 1 - X‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (exp_remainder X hX)

private lemma bracket_bound (X Y : Mat) :
    ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc
    _ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

private lemma exp_commutator_error (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (X Y : Mat) (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r)
    (hU : exp X ∈ unitary Mat) (hV : exp Y ∈ unitary Mat) :
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

private lemma exp_in_ball (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8)
    (X : Mat) (hX : ‖X‖ ≤ (3 / 4 : ℝ) * ε) :
    ‖1 - exp X‖ ≤ ε := by
  have hX1 : ‖X‖ ≤ 1 := by linarith
  rw [norm_sub_rev]
  calc
    _ ≤ ‖X‖ + ‖X‖ ^ 2 := exp_distance X hX1
    _ ≤ (3 / 4 : ℝ) * ε + ((3 / 4 : ℝ) * ε) ^ 2 := by gcongr
    _ ≤ ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεsmall)]

theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ A ∈ QAlgorithms.su2Ball (ε ^ 2),
        ∃ B ∈ QAlgorithms.su2Ball ε, ∃ C ∈ QAlgorithms.su2Ball ε,
          QAlgorithms.specNorm ((A : Matrix (Fin 2) (Fin 2) ℂ) -
            ((B * C * B⁻¹ * C⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
              Matrix (Fin 2) (Fin 2) ℂ)) ≤ K * ε ^ 3 := by
  obtain ⟨ε₀, hε₀, hf⟩ := QAlgorithms.Childs.su2_balanced_lie_bracket
  refine ⟨18, by norm_num, min ε₀ (1 / 8), lt_min hε₀ (by norm_num), ?_⟩
  intro ε hε hsmall A hA
  have hεsmall : ε ≤ 1 / 8 := hsmall.trans (min_le_right _ _)
  obtain ⟨X, Y, hX, hY, hU, hV, heq⟩ := hf ε hε (hsmall.trans (min_le_left _ _)) A hA
  let B : SU := ⟨exp X, hU⟩
  let C : SU := ⟨exp Y, hV⟩
  refine ⟨B, exp_in_ball ε hε hεsmall X hX, C, exp_in_ball ε hε hεsmall Y hY, ?_⟩
  change ‖(A : Mat) - exp X * exp Y * star (exp X) * star (exp Y)‖ ≤ _
  rw [heq]
  exact exp_commutator_error ε hε.le (by linarith) X Y
    (hX.trans (by linarith)) (hY.trans (by linarith)) hU.1 hV.1
