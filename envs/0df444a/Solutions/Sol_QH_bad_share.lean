-- Prove2me | solution 1 for QH.bad_share
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:14.651406+00:00
-- url     : https://prove2.me/submissions/3814bae9-82b6-4963-bcff-ec57f35f387e

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_BadShare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open scoped ArithmeticFunction.vonMangoldt
open Filter MeasureTheory
namespace QH
private theorem bs_continuous_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) : Continuous (fun y => S Z y q κ) := by
  unfold S cN
  refine continuous_finsetSum _ (fun m _ => ?_)
  fun_prop
private theorem bs_measurable_D (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) :
    Measurable (fun v => bsD Z v q κ) := by
  unfold bsD
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const
private theorem bs_norm_D_le (Z v : ℝ) (q : ℕ) (κ : ℕ → ℂ) :
    ‖bsD Z v q κ‖ ≤
      ∑ m ∈ Icc 1 ⌊Z⌋₊, ‖((Λ m : ℝ) : ℂ) * κ m * ((jacobiSym (m : ℤ) q : ℤ) : ℂ) / m‖ := by
  unfold bsD
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]; exact norm_nonneg _
private theorem bs_intervalIntegrable_D (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (a b : ℝ) :
    IntervalIntegrable (fun v => bsD Z v q κ) volume a b ∧
      IntervalIntegrable (fun v => ‖bsD Z v q κ‖ ^ 2) volume a b := by
  set C := ∑ m ∈ Icc 1 ⌊Z⌋₊, ‖((Λ m : ℝ) : ℂ) * κ m * ((jacobiSym (m : ℤ) q : ℤ) : ℂ) / m‖ with hC
  constructor
  · refine IntervalIntegrable.mono_fun' (g := fun _ => C) intervalIntegrable_const
      (bs_measurable_D Z q κ).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun v => bs_norm_D_le Z v q κ)
  · refine IntervalIntegrable.mono_fun' (g := fun _ => C ^ 2) intervalIntegrable_const
      ((bs_measurable_D Z q κ).norm.pow_const 2).aestronglyMeasurable ?_
    refine Eventually.of_forall (fun v => ?_)
    have := bs_norm_D_le Z v q κ
    simp only [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
private theorem bs_hasDeriv_min (m x : ℝ) (hm : 0 < m) :
    HasDerivWithinAt (fun y : ℝ => min 1 (y / m)) (if x < m then 1 / m else 0) (Set.Ioi x) x := by
  split_ifs with h
  · have h1 : HasDerivAt (fun y : ℝ => y / m) (1 / m) x := (hasDerivAt_id x).div_const m
    refine (h1.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Iio_mem_nhds h] with y hy
    exact min_eq_right ((div_le_one hm).2 (le_of_lt hy))
  · push Not at h
    have h1 : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Ioi x) x :=
      (hasDerivAt_const x 1).hasDerivWithinAt
    refine h1.congr (fun y hy => ?_) ?_
    · exact min_eq_left ((one_le_div hm).2 (h.trans (le_of_lt hy)))
    · exact min_eq_left ((one_le_div hm).2 h)
private theorem bs_hasDeriv_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (x : ℝ) :
    HasDerivWithinAt (fun y => S Z y q κ) (bsD Z x q κ) (Set.Ioi x) x := by
  unfold bsD S cN
  refine HasDerivWithinAt.fun_sum (fun m hm => ?_)
  have hm0 : (0 : ℝ) < m := by
    have := (Finset.mem_Icc.1 hm).1
    exact_mod_cast this
  have h1 := (((bs_hasDeriv_min m x hm0).const_mul (Λ m)).ofReal_comp.mul_const (κ m)).mul_const
    ((jacobiSym (m : ℤ) q : ℤ) : ℂ)
  refine HasDerivWithinAt.congr_deriv h1 ?_
  split_ifs
  · push_cast; ring
  · simp
private theorem bs_S_sub_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (a b : ℝ) :
    S Z b q κ - S Z a q κ = ∫ v in a..b, bsD Z v q κ := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right (f := fun y => S Z y q κ)
    (bs_continuous_S Z q κ).continuousOn (fun x _ => bs_hasDeriv_S Z q κ x)
    (bs_intervalIntegrable_D Z q κ a b).1
private theorem bs_mul_D_eq_S (Z : ℝ) (y : ℝ) (q : ℕ) (κ : ℕ → ℂ) :
    (y : ℂ) * bsD Z y q κ = S Z y q (fun m => if y < (m : ℝ) then κ m else 0) := by
  unfold bsD S cN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by
    have := (Finset.mem_Icc.1 hm).1
    exact_mod_cast this
  by_cases h : y < (m : ℝ)
  · simp only [h, if_true]
    rw [min_eq_right ((div_le_one hm0).2 h.le)]
    push_cast
    ring
  · simp [h]
private theorem bs_sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h1 : IntervalIntegrable f volume a b)
    (h2 : IntervalIntegrable (fun v => f v ^ 2) volume a b) :
    (∫ v in a..b, f v) ^ 2 ≤ (b - a) * ∫ v in a..b, f v ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  set I := ∫ v in a..b, f v with hI
  set A := ∫ v in a..b, f v ^ 2 with hA
  have hL : 0 < b - a := sub_pos.2 h
  have h0 : 0 ≤ ∫ v in a..b, (((b - a) ^ 2 * f v ^ 2 - (2 * (b - a) * I) * f v) + I ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hab (fun v => by
      nlinarith [sq_nonneg ((b - a) * f v - I)])
  rw [intervalIntegral.integral_add ((h2.const_mul _).sub (h1.const_mul _))
      intervalIntegrable_const,
    intervalIntegral.integral_sub (h2.const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hI, ← hA, smul_eq_mul] at h0
  have h3 : (b - a) * I ^ 2 ≤ (b - a) * ((b - a) * A) := by nlinarith
  exact le_of_mul_le_mul_left h3 hL
private theorem bs_normSq_S_le (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) {Y W y : ℝ} (hW : W ≤ 2 * Y)
    (hY : 0 ≤ Y) (hy : y ∈ Set.Icc Y W) :
    ‖S Z y q κ‖ ^ 2 ≤ 2 * ‖S Z Y q κ‖ ^ 2 + 2 * Y * ∫ v in Y..W, ‖bsD Z v q κ‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hy
  have hS : S Z y q κ = S Z Y q κ + ∫ v in Y..y, bsD Z v q κ := by
    rw [← bs_S_sub_S]; ring
  have hn : ‖∫ v in Y..y, bsD Z v q κ‖ ≤ ∫ v in Y..y, ‖bsD Z v q κ‖ :=
    intervalIntegral.norm_integral_le_integral_norm h1
  have hcs := bs_sq_integral_le (f := fun v => ‖bsD Z v q κ‖) h1
    (bs_intervalIntegrable_D Z q κ Y y).1.norm (bs_intervalIntegrable_D Z q κ Y y).2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (bs_intervalIntegrable_D Z q κ Y y).2 (bs_intervalIntegrable_D Z q κ y W).2
  have hA : 0 ≤ ∫ v in Y..y, ‖bsD Z v q κ‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall h1 (fun v => sq_nonneg _)
  have hB : 0 ≤ ∫ v in y..W, ‖bsD Z v q κ‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall h2 (fun v => sq_nonneg _)
  have htri : ‖S Z y q κ‖ ≤ ‖S Z Y q κ‖ + ∫ v in Y..y, ‖bsD Z v q κ‖ := by
    rw [hS]; exact (norm_add_le _ _).trans (by linarith)
  rw [← hadd]
  set I := ∫ v in Y..y, ‖bsD Z v q κ‖
  set A := ∫ v in Y..y, ‖bsD Z v q κ‖ ^ 2
  set B := ∫ v in y..W, ‖bsD Z v q κ‖ ^ 2
  have h3 : ‖S Z y q κ‖ ^ 2 ≤ (‖S Z Y q κ‖ + I) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h4 : (y - Y) * A ≤ Y * A := mul_le_mul_of_nonneg_right (by linarith) hA
  have h5 : 0 ≤ Y * B := mul_nonneg hY hB
  nlinarith [sq_nonneg (‖S Z Y q κ‖ - I)]
private theorem bs_sum_D_le {C Z : ℝ} {P : Finset ℕ} {A : Set ℝ} (h : MeanSq C Z P A) {y : ℝ}
    (hy : y ∈ A) (hy0 : 0 < y) {κ : ℕ → ℂ} (hκ : ∀ m, ‖κ m‖ ≤ 1) :
    ∑ q ∈ P, ‖bsD Z y q κ‖ ^ 2 ≤ C * Real.log y * P.card / y := by
  have h1 := h y hy (fun m => if y < (m : ℝ) then κ m else 0) (fun m => by
    by_cases hm : y < (m : ℝ)
    · simpa [hm] using hκ m
    · simp [hm])
  have h2 : ∀ q, ‖S Z y q (fun m => if y < (m : ℝ) then κ m else 0)‖ ^ 2
      = y ^ 2 * ‖bsD Z y q κ‖ ^ 2 := by
    intro q
    rw [← bs_mul_D_eq_S Z y q κ, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [h2] at h1
  rw [← Finset.mul_sum] at h1
  rw [le_div_iff₀ hy0]
  refine le_of_mul_le_mul_left ?_ hy0
  nlinarith [h1]
private theorem bs_block {C Z Y W : ℝ} {P : Finset ℕ} (hC : 0 ≤ C) (hY : 1 ≤ Y) (hYW : Y ≤ W)
    (hW2 : W ≤ 2 * Y) (h : MeanSq C Z P (Set.Icc Y W)) {κ : ℕ → ℂ} (hκ : ∀ m, ‖κ m‖ ≤ 1)
    (w : ℕ → ℝ) (hw : ∀ q, w q ∈ Set.Icc Y W) :
    ∑ q ∈ P, ‖S Z (w q) q κ‖ ^ 2 ≤ 4 * C * Y * Real.log (2 * Y) * P.card := by
  have hY0 : 0 < Y := by linarith
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have h1 : ∑ q ∈ P, ‖S Z (w q) q κ‖ ^ 2 ≤
      ∑ q ∈ P, (2 * ‖S Z Y q κ‖ ^ 2 + (2 * Y) * ∫ v in Y..W, ‖bsD Z v q κ‖ ^ 2) :=
    Finset.sum_le_sum fun q _ => bs_normSq_S_le Z q κ hW2 hY0.le (hw q)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 := h Y ⟨le_rfl, hYW⟩ κ hκ
  have hL : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hLY : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
  have hint : IntervalIntegrable (fun v => ∑ q ∈ P, ‖bsD Z v q κ‖ ^ 2) volume Y W := by
    have := IntervalIntegrable.sum (μ := volume) (a := Y) (b := W) P
      (f := fun q v => ‖bsD Z v q κ‖ ^ 2) (fun q _ => (bs_intervalIntegrable_D Z q κ Y W).2)
    have e : (fun v => ∑ q ∈ P, ‖bsD Z v q κ‖ ^ 2) = ∑ q ∈ P, fun v => ‖bsD Z v q κ‖ ^ 2 := by
      funext v
      simp [Finset.sum_apply]
    rw [e]
    exact this
  rw [← intervalIntegral.integral_finsetSum
    (fun q _ => (bs_intervalIntegrable_D Z q κ Y W).2)] at h1
  set K := C * Real.log (2 * Y) * P.card with hK
  have hK0 : 0 ≤ K := by positivity
  have h4 : (∫ v in Y..W, ∑ q ∈ P, ‖bsD Z v q κ‖ ^ 2) ≤ ∫ _ in Y..W, K / Y := by
    refine intervalIntegral.integral_mono_on hYW hint intervalIntegrable_const ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hY0 hx.1
    refine (bs_sum_D_le h hx hx0 hκ).trans ?_
    have : Real.log x ≤ Real.log (2 * Y) := Real.log_le_log hx0 (hx.2.trans hW2)
    refine div_le_div₀ hK0 ?_ hY0 hx.1
    rw [hK]
    gcongr
  rw [intervalIntegral.integral_const, smul_eq_mul] at h4
  have h5 : (W - Y) * (K / Y) ≤ K := by
    calc (W - Y) * (K / Y) ≤ Y * (K / Y) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K := by field_simp
  have h7 := mul_le_mul_of_nonneg_left (h4.trans h5) (show 0 ≤ 2 * Y by positivity)
  have h8 : C * Y * Real.log Y * P.card ≤ C * Y * Real.log (2 * Y) * P.card := by gcongr
  have h9 : 2 * Y * K = 2 * (C * Y * Real.log (2 * Y) * P.card) := by rw [hK]; ring
  linarith
private theorem bs_markov {C τ Z Y W : ℝ} {P B : Finset ℕ} (hC : 0 ≤ C) (hτ : 0 < τ) (hY : 2 ≤ Y)
    (hYW : Y ≤ W) (hW2 : W ≤ 2 * Y) (h : MeanSq C Z P (Set.Icc Y W)) {κ : ℕ → ℂ}
    (hκ : ∀ m, ‖κ m‖ ≤ 1) (hBP : B ⊆ P)
    (hB : ∀ q ∈ B, ∃ y ∈ Set.Icc Y W, y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖) :
    (B.card : ℝ) ≤ 32 * C / τ * Y ^ (-τ) * P.card := by
  have hY0 : 0 < Y := by linarith
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hex : ∀ q, ∃ y ∈ Set.Icc Y W, q ∈ B → y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖ := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨y, hy, hy'⟩ := hB q hq
      exact ⟨y, hy, fun _ => hy'⟩
    · exact ⟨Y, ⟨le_rfl, hYW⟩, fun h => absurd h hq⟩
  choose w hw hw' using hex
  have h1 := bs_block hC (by linarith) hYW hW2 h hκ w hw
  have h2 : ∑ q ∈ B, ‖S Z (w q) q κ‖ ^ 2 ≤ ∑ q ∈ P, ‖S Z (w q) q κ‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hBP (fun q _ _ => sq_nonneg _)
  have ht : 0 < Y ^ τ := Real.rpow_pos_of_pos hY0 τ
  have e : (Y ^ (1 / 2 + τ) / 2) ^ 2 = Y * Y ^ τ * Y ^ τ / 4 := by
    rw [div_pow, sq (Y ^ _), ← Real.rpow_add hY0,
      show 1 / 2 + τ + (1 / 2 + τ) = 1 + τ + τ by ring, Real.rpow_add hY0, Real.rpow_add hY0,
      Real.rpow_one]
    norm_num
  have h3 : (B.card : ℝ) * (Y * Y ^ τ * Y ^ τ / 4) ≤ ∑ q ∈ B, ‖S Z (w q) q κ‖ ^ 2 := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ (fun q hq => ?_)
    rw [← e]
    refine pow_le_pow_left₀ (by positivity) (le_trans ?_ (hw' q hq).le) 2
    have : Y ^ (1 / 2 + τ) ≤ w q ^ (1 / 2 + τ) :=
      Real.rpow_le_rpow hY0.le (hw q).1 (by linarith)
    linarith
  have h4 : Real.log (2 * Y) ≤ 2 * (Y ^ τ / τ) := by
    have a1 := Real.log_le_rpow_div hY0.le hτ
    have a2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    rw [Real.log_mul (by norm_num) hY0.ne']
    linarith
  have h5 : 4 * C * Y * Real.log (2 * Y) * P.card ≤ 4 * C * Y * (2 * (Y ^ τ / τ)) * P.card := by
    gcongr
  have hpos : 0 < Y * Y ^ τ * Y ^ τ / 4 := by positivity
  refine le_of_mul_le_mul_right (h3.trans (h2.trans (h1.trans (h5.trans (le_of_eq ?_))))) hpos
  rw [Real.rpow_neg hY0.le]
  field_simp
  ring
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open scoped ArithmeticFunction.vonMangoldt
open Filter MeasureTheory
open QH
namespace QH
theorem _root_.solution :
    ∀ C τ η : ℝ, 0 ≤ C → 0 < τ → 0 < η → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (X Z : ℝ) (P B : Finset ℕ) (κ : ℕ → ℂ),
      (∀ n, ‖κ n‖ ≤ 1) → MeanSq C Z P (Set.Icc Y X) → B ⊆ P →
      (∀ q ∈ B, ∃ y ∈ Set.Icc Y X, y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖) → (B.card : ℝ) ≤ η * P.card := by
  classical
  intro C τ η hC hτ hη
  set r : ℝ := (2 : ℝ) ^ (-τ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlim : Tendsto (fun Y : ℝ => 32 * C / τ * Y ^ (-τ) * (1 - r)⁻¹) atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop hτ).const_mul (32 * C / τ)).mul_const (1 - r)⁻¹
    simpa using this
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    ((hlim.eventually (ge_mem_nhds hη)).and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨Y₀, fun Y hY X Z P B κ hκ hM hBP hB => ?_⟩
  obtain ⟨hη', hY2⟩ := hY₀ Y hY
  have hY0 : 0 < Y := by linarith
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hidx : ∀ q, ∃ i : ℕ, q ∈ B → 2 ^ i * Y ≤ X ∧
      ∃ y ∈ Set.Icc (2 ^ i * Y) (min (2 * (2 ^ i * Y)) X), y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖ := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨y, ⟨h1, h2⟩, hy'⟩ := hB q hq
      have h3 : 1 ≤ y / Y := by rw [le_div_iff₀ hY0]; linarith
      obtain ⟨i, hi1, hi2⟩ := exists_nat_pow_near h3 (by norm_num : (1 : ℝ) < 2)
      rw [le_div_iff₀ hY0] at hi1
      rw [div_lt_iff₀ hY0, pow_succ] at hi2
      refine ⟨i, fun _ => ⟨hi1.trans h2, y, ⟨hi1, le_min ?_ h2⟩, hy'⟩⟩
      nlinarith
    · exact ⟨0, fun h => absurd h hq⟩
  choose f hf using hidx
  have hcard : (B.card : ℝ) = ∑ i ∈ B.image f, ((B.filter (fun q => f q = i)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_image f B]
    push_cast
    rfl
  have hblock : ∀ i ∈ B.image f, ((B.filter (fun q => f q = i)).card : ℝ) ≤
      32 * C / τ * Y ^ (-τ) * P.card * r ^ i := by
    intro i hi
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hi
    have hX := (hf q₀ hq₀).1
    have h1 : (1 : ℝ) ≤ 2 ^ f q₀ := one_le_pow₀ (by norm_num)
    have hYY : Y ≤ 2 ^ f q₀ * Y := by nlinarith
    have := bs_markov (Y := 2 ^ f q₀ * Y) (W := min (2 * (2 ^ f q₀ * Y)) X) (P := P) (Z := Z)
      (B := B.filter (fun q => f q = f q₀)) hC hτ (by linarith) (le_min (by linarith) hX)
      (min_le_left _ _)
      (fun y hy => hM y ⟨hYY.trans hy.1, hy.2.trans (min_le_right _ _)⟩) hκ
      ((Finset.filter_subset _ _).trans hBP)
      (fun q hq => by
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
        rw [← hq2]
        exact (hf q hq1).2)
    refine this.trans (le_of_eq ?_)
    have e : ((2 : ℝ) ^ f q₀ * Y) ^ (-τ) = Y ^ (-τ) * r ^ f q₀ := by
      rw [hr, Real.mul_rpow (by positivity) hY0.le, mul_comm, ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
        mul_comm (f q₀ : ℝ)]
    rw [e]
    ring
  have hg : ∑ i ∈ B.image f, r ^ i ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
  calc (B.card : ℝ) ≤ ∑ i ∈ B.image f, 32 * C / τ * Y ^ (-τ) * P.card * r ^ i := by
        rw [hcard]; exact Finset.sum_le_sum hblock
    _ = 32 * C / τ * Y ^ (-τ) * P.card * ∑ i ∈ B.image f, r ^ i := by rw [Finset.mul_sum]
    _ ≤ 32 * C / τ * Y ^ (-τ) * P.card * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 32 * C / τ * Y ^ (-τ) * (1 - r)⁻¹ * P.card := by ring
    _ ≤ η * P.card := mul_le_mul_of_nonneg_right hη' hP
end QH
