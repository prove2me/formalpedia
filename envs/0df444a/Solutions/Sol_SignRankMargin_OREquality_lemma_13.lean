-- Prove2me | solution 1 for SignRankMargin.OREquality.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:53:52.780836+00:00
-- url     : https://prove2.me/submissions/997587ec-5e81-414b-9634-70fbf58110b2

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_Geometry
import Theorems.Thm_SignRankMargin_OREquality_lemma_11
import Theorems.Thm_SignRankMargin_OREquality_lemma_12

section
namespace SignRankMargin.OREquality.Dev.L13

/-- Pairing bound: the operator norm controls the bilinear pairing of row and column vectors. -/
lemma pairing_le {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {r : ℕ} (A : Matrix X Y ℝ) (K : ℝ)
    (hK : ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤ K)
    (U : X → EuclideanSpace ℝ (Fin r)) (V : Y → EuclideanSpace ℝ (Fin r)) :
    ∑ x, ∑ y, A x y * inner ℝ (U x) (V y) ≤
      K * Real.sqrt (∑ x, ‖U x‖ ^ 2) * Real.sqrt (∑ y, ‖V y‖ ^ 2) := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hK
  let Ul : Fin r → EuclideanSpace ℝ X := fun l => WithLp.toLp 2 (fun x => U x l)
  let Vl : Fin r → EuclideanSpace ℝ Y := fun l => WithLp.toLp 2 (fun y => V y l)
  have h1 : ∑ x, ∑ y, A x y * inner ℝ (U x) (V y) =
      ∑ l, inner ℝ (Ul l) (Matrix.toEuclideanLin A (Vl l)) := by
    simp only [PiLp.inner_apply, Ul, Vl, Matrix.toEuclideanLin_toLp]
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, RCLike.inner_apply, conj_trivial,
      Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  have h2 : ∀ l, inner ℝ (Ul l) (Matrix.toEuclideanLin A (Vl l)) ≤ K * (‖Ul l‖ * ‖Vl l‖) := by
    intro l
    calc _ ≤ ‖Ul l‖ * ‖Matrix.toEuclideanLin A (Vl l)‖ := real_inner_le_norm _ _
      _ ≤ ‖Ul l‖ * (K * ‖Vl l‖) := by
          gcongr
          have := (Matrix.toEuclideanLin A).toContinuousLinearMap.le_opNorm (Vl l)
          exact le_trans this (by gcongr)
      _ = _ := by ring
  have h3 : ∑ l, ‖Ul l‖ ^ 2 = ∑ x, ‖U x‖ ^ 2 := by
    simp only [Ul, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_comm]
  have h4 : ∑ l, ‖Vl l‖ ^ 2 = ∑ y, ‖V y‖ ^ 2 := by
    simp only [Vl, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_comm]
  rw [h1]
  calc _ ≤ ∑ l, K * (‖Ul l‖ * ‖Vl l‖) := Finset.sum_le_sum (fun l _ => h2 l)
    _ = K * ∑ l, ‖Ul l‖ * ‖Vl l‖ := by rw [Finset.mul_sum]
    _ ≤ K * (Real.sqrt (∑ l, ‖Ul l‖ ^ 2) * Real.sqrt (∑ l, ‖Vl l‖ ^ 2)) := by
        gcongr
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by rw [h3, h4]; ring

end SignRankMargin.OREquality.Dev.L13

namespace SignRankMargin.OREquality

set_option maxHeartbeats 4000000 in
open SignRankMargin.OREquality.Dev.L13 in
theorem chk_lemma_13 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Nonempty X] [Nonempty Y] (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (F : Matrix X Y Bool)
    (hsparse : (oneCount F : ℝ) ≤ (((d : ℝ) * L) ^ (6 * d))⁻¹ *
      (Fintype.card X : ℝ) * (Fintype.card Y : ℝ))
    (hwitness : ∃ A : Matrix X Y ℝ,
      (∀ x y, F x y = false → A x y ≤ -1) ∧
      uniformAverage (fun x y => |A x y|) ≤ L ∧
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤
        Real.sqrt ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) / (d : ℝ)) :
    d ≤ signRank F := by
  classical
  obtain ⟨A, hA1, hA2, hA3⟩ := hwitness
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ : ∃ r, signRank F = r := ⟨_, rfl⟩
  obtain ⟨u, v, hreal, havg⟩ := lemma_11 F r hr
  rw [hr] at hlt
  obtain ⟨x0⟩ := ‹Nonempty X›
  have hr1 : 1 ≤ r := by
    by_contra h0
    have : r = 0 := by omega
    subst this
    have h1 := hreal.1 x0
    have : u x0 = 0 := Subsingleton.elim _ _
    rw [this] at h1
    simp at h1
  -- real parameters
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (d : ℝ) * L := ⟨_, rfl⟩
  have hD2 : 2 ≤ D := by rw [hD]; nlinarith
  have hD1 : 1 ≤ D := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (D ^ (6 * d))⁻¹ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (D ^ 3)⁻¹ := ⟨_, rfl⟩
  rw [← hD, ← hη] at hsparse
  have hDp : 0 < D := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hD3 : 8 ≤ D ^ 3 := by nlinarith [sq_nonneg D]
  have hτ8 : τ ≤ 1 / 8 := by
    rw [hτ, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hD3
  have hτ1 : τ < 1 := by linarith
  have hD6le : D ^ 6 ≤ D ^ (6 * d) := pow_le_pow_right₀ hD1 (by omega)
  have hη1 : η < 1 := by
    rw [hη]
    have : 1 < D ^ (6 * d) := lt_of_lt_of_le (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hD2 6]) hD6le
    exact inv_lt_one_of_one_lt₀ this
  obtain ⟨E, G, hEG, hpos⟩ := lemma_12 F η hη0 hη1 hsparse r u v hreal τ hτ0 hτ1
  obtain ⟨hu, hv, hstrict⟩ := hreal
  -- bound on delta
  have hτsq : τ ^ 2 = (D ^ 6)⁻¹ := by rw [hτ, ← inv_pow, ← pow_mul, inv_pow]
  have hδ : 2 * Real.sqrt (η * (1 + 4 / τ) ^ r) ≤ 2 * τ := by
    have h14 : 1 + 4 / τ ≤ D ^ 6 := by
      rw [hτ, div_inv_eq_mul]
      have : D ^ 6 = D ^ 3 * D ^ 3 := by ring
      nlinarith [hD3]
    have hX : (1 + 4 / τ) ^ r ≤ D ^ (6 * r) := by
      have h4 : 0 < 4 / τ := by positivity
      rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) h14 r
    have hY : D ^ (6 * r) * D ^ 6 ≤ D ^ (6 * d) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hD1 (by omega)
    have hZ : η * (1 + 4 / τ) ^ r ≤ τ ^ 2 := by
      rw [hη, hτsq, inv_mul_le_iff₀ (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      exact le_trans (mul_le_mul_of_nonneg_right hX (by positivity)) hY
    have := Real.sqrt_le_sqrt hZ
    rw [Real.sqrt_sq hτ0.le] at this
    linarith
  have hH1 : ∀ x y, |inner ℝ (u x) (v y)| ≤ 1 := fun x y => by
    calc _ ≤ ‖u x‖ * ‖v y‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hu, hv]; norm_num
  let u' : X → EuclideanSpace ℝ (Fin r) := fun x => if x ∈ E then 0 else u x
  let v' : Y → EuclideanSpace ℝ (Fin r) := fun y => if y ∈ G then 0 else v y
  have hu' : ∀ x, ‖u' x‖ ≤ 1 := fun x => by
    by_cases h : x ∈ E <;> simp [u', h, hu]
  have hv' : ∀ y, ‖v' y‖ ≤ 1 := fun y => by
    by_cases h : y ∈ G <;> simp [v', h, hv]
  let B : Matrix X Y ℝ := fun x y => inner ℝ (u' x) (v' y)
  have hB : ∀ x y, B x y = if x ∈ E ∨ y ∈ G then 0 else inner ℝ (u x) (v y) := by
    intro x y
    by_cases hx : x ∈ E <;> by_cases hy : y ∈ G <;> simp [B, u', v', hx, hy]
  have hBF : ∀ x y, F x y = false → -1 ≤ B x y ∧ B x y ≤ 0 := by
    intro x y hF
    rw [hB]
    split_ifs
    · norm_num
    · have h1 := hstrict x y
      rw [hF] at h1
      simp only [Bool.false_eq_true, if_false] at h1
      have h2 := abs_le.1 (hH1 x y)
      exact ⟨h2.1, h1.le⟩
  have hBT : ∀ x y, F x y = true → 0 ≤ B x y ∧ B x y ≤ τ := by
    intro x y hF
    rw [hB]
    split_ifs with h
    · exact ⟨le_refl _, hτ0.le⟩
    · push Not at h
      obtain ⟨hp, hq⟩ := hpos x y hF h.1 h.2
      exact ⟨hp.le, hq⟩
  have hBsq : ∀ x y, B x y ^ 2 ≤ 1 := by
    intro x y
    rw [hB]; split_ifs
    · norm_num
    · exact sq_le_one_iff_abs_le_one _ |>.2 (hH1 x y)
  set nX : ℝ := (Fintype.card X : ℝ) with hnX
  set nY : ℝ := (Fintype.card Y : ℝ) with hnY
  have hnXp : 0 < nX := by rw [hnX]; exact_mod_cast Fintype.card_pos
  have hnYp : 0 < nY := by rw [hnY]; exact_mod_cast Fintype.card_pos
  have hMp : 0 < nX * nY := mul_pos hnXp hnYp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrd : (r : ℝ) ≤ d - 1 := by
    have : r + 1 ≤ d := hlt
    have : (r : ℝ) + 1 ≤ d := by exact_mod_cast this
    linarith
  -- sum of squares of H
  have hHsq : ∑ x, ∑ y, inner ℝ (u x) (v y) ^ 2 = 1 / r * (nX * nY) := by
    unfold uniformAverage at havg
    simp only [sq_abs] at havg
    exact (div_eq_iff hMp.ne').1 havg
  -- lower bound for sum of squares of B
  have hS1 : ∑ x, ∑ y, inner ℝ (u x) (v y) ^ 2 - nX * nY * (2 * Real.sqrt (η * (1 + 4 / τ) ^ r)) ≤
      ∑ x, ∑ y, B x y ^ 2 := by
    have hpt : ∀ x y, inner ℝ (u x) (v y) ^ 2 - B x y ^ 2 ≤
        (if x ∈ E then (1:ℝ) else 0) + (if y ∈ G then (1:ℝ) else 0) := by
      intro x y
      have h1 : inner ℝ (u x) (v y) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hH1 x y)
      have e1 : (0:ℝ) ≤ (if x ∈ E then (1:ℝ) else 0) := by split_ifs <;> norm_num
      have e2 : (0:ℝ) ≤ (if y ∈ G then (1:ℝ) else 0) := by split_ifs <;> norm_num
      have hB2 : 0 ≤ B x y ^ 2 := sq_nonneg _
      by_cases hx : x ∈ E
      · have : B x y = 0 := by rw [hB]; simp [hx]
        rw [this, if_pos hx]; linarith
      · by_cases hy : y ∈ G
        · have : B x y = 0 := by rw [hB]; simp [hy]
          rw [this, if_pos hy]; linarith
        · have : B x y = inner ℝ (u x) (v y) := by rw [hB]; simp [hx, hy]
          rw [this]; linarith
    have hsum : ∑ x, ∑ y, ((if x ∈ E then (1:ℝ) else 0) + (if y ∈ G then (1:ℝ) else 0)) =
        nY * E.card + nX * G.card := by
      simp [Finset.sum_add_distrib, Finset.sum_boole, hnX, hnY, mul_comm]
    have h2 : ∑ x, ∑ y, (inner ℝ (u x) (v y) ^ 2 - B x y ^ 2) ≤ nY * E.card + nX * G.card := by
      rw [← hsum]
      exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hpt x y))
    have h3 : nY * E.card + nX * G.card = nX * nY * ((E.card : ℝ) / nX + (G.card : ℝ) / nY) := by
      field_simp
    have h4 : nX * nY * ((E.card : ℝ) / nX + (G.card : ℝ) / nY) ≤
        nX * nY * (2 * Real.sqrt (η * (1 + 4 / τ) ^ r)) :=
      mul_le_mul_of_nonneg_left hEG hMp.le
    simp only [Finset.sum_sub_distrib] at h2
    linarith
  -- sparse positive part
  have hS2 : ∑ x, ∑ y, B x y ^ 2 ≤ τ ^ 2 * (η * nX * nY) +
      ∑ x, ∑ y, (if F x y = true then (0:ℝ) else B x y ^ 2) := by
    have hone : τ ^ 2 * (oneCount F : ℝ) = ∑ x, ∑ y, (if F x y = true then τ ^ 2 else (0:ℝ)) := by
      unfold oneCount
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs <;> simp
    have hle : τ ^ 2 * (oneCount F : ℝ) ≤ τ ^ 2 * (η * nX * nY) :=
      mul_le_mul_of_nonneg_left hsparse (by positivity)
    have hpt : ∀ x y, B x y ^ 2 ≤
        (if F x y = true then τ ^ 2 else (0:ℝ)) + (if F x y = true then (0:ℝ) else B x y ^ 2) := by
      intro x y
      cases hF : F x y
      · simp
      · obtain ⟨h1, h2⟩ := hBT x y hF
        simp only [if_true, zero_add]
        nlinarith
    have : ∑ x, ∑ y, B x y ^ 2 ≤ ∑ x, ∑ y, ((if F x y = true then τ ^ 2 else (0:ℝ)) +
        (if F x y = true then (0:ℝ) else B x y ^ 2)) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hpt x y))
    simp only [Finset.sum_add_distrib] at this
    linarith
  -- lower bound for the pairing
  have hAabs : ∑ x, ∑ y, |A x y| ≤ L * (nX * nY) := by
    unfold uniformAverage at hA2
    exact (div_le_iff₀ hMp).1 hA2
  have hS3 : ∑ x, ∑ y, (if F x y = true then (0:ℝ) else B x y ^ 2) - τ * (L * (nX * nY)) ≤
      ∑ x, ∑ y, A x y * B x y := by
    have hpt : ∀ x y, (if F x y = true then (0:ℝ) else B x y ^ 2) - τ * |A x y| ≤ A x y * B x y := by
      intro x y
      cases hF : F x y
      · simp only [Bool.false_eq_true, if_false]
        obtain ⟨h1, h2⟩ := hBF x y hF
        have h3 := hA1 x y hF
        have h4 : 0 ≤ -(B x y) * (B x y - A x y) :=
          mul_nonneg (neg_nonneg.2 h2) (sub_nonneg.2 (by linarith))
        have h5 := mul_nonneg hτ0.le (abs_nonneg (A x y))
        nlinarith
      · simp only [if_true, zero_sub]
        obtain ⟨h1, h2⟩ := hBT x y hF
        have h6 : 0 ≤ (A x y + |A x y|) * B x y :=
          mul_nonneg (by linarith [neg_abs_le (A x y)]) h1
        have h7 : |A x y| * B x y ≤ |A x y| * τ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        nlinarith
    have : ∑ x, ∑ y, ((if F x y = true then (0:ℝ) else B x y ^ 2) - τ * |A x y|) ≤
        ∑ x, ∑ y, A x y * B x y :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hpt x y))
    have e : ∑ x, ∑ y, ((if F x y = true then (0:ℝ) else B x y ^ 2) - τ * |A x y|) =
        ∑ x, ∑ y, (if F x y = true then (0:ℝ) else B x y ^ 2) - τ * ∑ x, ∑ y, |A x y| := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e] at this
    have h5 : τ * ∑ x, ∑ y, |A x y| ≤ τ * (L * (nX * nY)) := mul_le_mul_of_nonneg_left hAabs hτ0.le
    linarith
  -- upper bound for the pairing
  have hS4 : ∑ x, ∑ y, A x y * B x y ≤ nX * nY / d := by
    have hp := pairing_le A _ hA3 u' v'
    have hsu : ∑ x, ‖u' x‖ ^ 2 ≤ nX := by
      calc ∑ x, ‖u' x‖ ^ 2 ≤ ∑ _x : X, (1:ℝ) :=
            Finset.sum_le_sum (fun x _ => pow_le_one₀ (norm_nonneg _) (hu' x))
        _ = nX := by simp [hnX]
    have hsv : ∑ y, ‖v' y‖ ^ 2 ≤ nY := by
      calc ∑ y, ‖v' y‖ ^ 2 ≤ ∑ _y : Y, (1:ℝ) :=
            Finset.sum_le_sum (fun y _ => pow_le_one₀ (norm_nonneg _) (hv' y))
        _ = nY := by simp [hnY]
    have hK : 0 ≤ Real.sqrt (nX * nY) / d := by positivity
    have h1 : Real.sqrt (nX * nY) / d * Real.sqrt (∑ x, ‖u' x‖ ^ 2) * Real.sqrt (∑ y, ‖v' y‖ ^ 2) ≤
        Real.sqrt (nX * nY) / d * Real.sqrt nX * Real.sqrt nY := by
      gcongr
    have h2 : Real.sqrt (nX * nY) / d * Real.sqrt nX * Real.sqrt nY = nX * nY / d := by
      have hsq : Real.sqrt nX * Real.sqrt nY = Real.sqrt (nX * nY) := (Real.sqrt_mul hnXp.le _).symm
      have hss : Real.sqrt (nX * nY) * Real.sqrt (nX * nY) = nX * nY := Real.mul_self_sqrt hMp.le
      calc Real.sqrt (nX * nY) / d * Real.sqrt nX * Real.sqrt nY
          = (Real.sqrt (nX * nY) * (Real.sqrt nX * Real.sqrt nY)) / d := by ring
        _ = nX * nY / d := by rw [hsq, hss]
    exact le_trans hp (h2 ▸ h1)
  -- combine
  have hkey : nX * nY * (1 / r - 1 / d - 2 * Real.sqrt (η * (1 + 4 / τ) ^ r) - η * τ ^ 2 - L * τ) ≤ 0 := by
    have : nX * nY / d = nX * nY * (1 / d) := by ring
    nlinarith
  have hkey2 : 1 / (r : ℝ) - 1 / d ≤ 2 * Real.sqrt (η * (1 + 4 / τ) ^ r) + η * τ ^ 2 + L * τ := by
    by_contra hcon
    push Not at hcon
    have := mul_pos hMp (sub_pos.2 hcon)
    nlinarith
  -- final arithmetic
  have hdp : (0:ℝ) < d := by linarith
  have hητ : η ≤ τ ^ 2 := by
    rw [hη, hτsq]; exact inv_anti₀ (by positivity) hD6le
  have hτ4 : η * τ ^ 2 < τ := by
    have h1 : η * τ ^ 2 ≤ τ ^ 2 * τ ^ 2 := mul_le_mul_of_nonneg_right hητ (by positivity)
    have h2 : τ ^ 2 * τ ^ 2 < τ := by nlinarith [mul_pos hτ0 hτ0, mul_pos (mul_pos hτ0 hτ0) hτ0]
    linarith
  have hd3 : (0:ℝ) < (d:ℝ) ^ 3 := by positivity
  have hτw : τ ≤ 1 / (d:ℝ) ^ 3 := by
    rw [hτ, hD, mul_pow, inv_eq_one_div]
    apply one_div_le_one_div_of_le hd3
    have : (1:ℝ) ≤ L ^ 3 := one_le_pow₀ hL
    nlinarith
  have hLτ : L * τ ≤ 1 / (d:ℝ) ^ 3 := by
    have hL0 : 0 < L := by linarith
    have : L * τ = (1 / L ^ 2) * (1 / (d:ℝ) ^ 3) := by
      rw [hτ, hD, mul_pow]; field_simp
    rw [this]
    have : 1 / L ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h0 : 0 ≤ 1 / (d:ℝ) ^ 3 := by positivity
    nlinarith
  have hupper : 1 / (r : ℝ) - 1 / d < 4 / (d:ℝ) ^ 3 := by
    have : 4 / (d:ℝ) ^ 3 = 1 / (d:ℝ) ^ 3 + 1 / (d:ℝ) ^ 3 + 1 / (d:ℝ) ^ 3 + 1 / (d:ℝ) ^ 3 := by ring
    linarith
  have hlow : 4 / (d:ℝ) ^ 3 ≤ 1 / ((d:ℝ) - 1) - 1 / d := by
    have hd1 : (0:ℝ) < d - 1 := by linarith
    rw [div_sub_div _ _ hd1.ne' hdp.ne', div_le_div_iff₀ hd3 (mul_pos hd1 hdp)]
    nlinarith [mul_nonneg hdp.le (sq_nonneg ((d:ℝ) - 2))]
  have hr1' : 1 / ((d:ℝ) - 1) ≤ 1 / (r : ℝ) :=
    one_div_le_one_div_of_le (by linarith) hrd
  linarith

end SignRankMargin.OREquality
end

theorem solution : type_of% @SignRankMargin.OREquality.chk_lemma_13 := @SignRankMargin.OREquality.chk_lemma_13
