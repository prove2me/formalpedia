-- Prove2me | solution 1 for StrictCompatLB.MeanField.supermarket_ode_exists_in_Y
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:54:34.499524+00:00
-- url     : https://prove2.me/submissions/6baa83d4-ba73-40e3-9a21-1c5e9bd0b134

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SC77K7

/-! K7 work: ODE well-posedness in 𝒴. State space ℓ¹ for `y i = x (i+1)`; the drift is made
globally Lipschitz by clamping coordinates into `[0,1]` inside the powers (no effect on 𝒴). -/

abbrev L1 := lp (fun _ : ℕ => ℝ) 1

lemma summable_abs (y : L1) : Summable fun i => |y i| := by
  have := (lp.memℓp y).summable (by norm_num : 0 < (1:ℝ≥0∞).toReal)
  simpa [Real.norm_eq_abs] using this

lemma norm_eq (y : L1) : ‖y‖ = ∑' i, |y i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]; simp [Real.norm_eq_abs]

lemma tsum_shift_le {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ i, 0 ≤ f i) :
    ∑' i, f (i + 1) ≤ ∑' i, f i := by
  rw [hf.tsum_eq_zero_add]; linarith [h0 0]

/-- `x i = 1` for `i = 0`, else `y (i-1)`. -/
def xs (y : L1) (i : ℕ) : ℝ := if i = 0 then 1 else y (i - 1)

@[simp] lemma xs_zero (y : L1) : xs y 0 = 1 := by simp [xs]
@[simp] lemma xs_succ (y : L1) (i : ℕ) : xs y (i + 1) = y i := by simp [xs]

def clamp (u : ℝ) : ℝ := max 0 (min u 1)

lemma clamp_nonneg (u : ℝ) : 0 ≤ clamp u := le_max_left _ _
lemma clamp_le_one (u : ℝ) : clamp u ≤ 1 := max_le zero_le_one (min_le_right _ _)
lemma clamp_le_abs (u : ℝ) : clamp u ≤ |u| :=
  max_le (abs_nonneg _) ((min_le_left _ _).trans (le_abs_self _))
lemma clamp_lip (a b : ℝ) : |clamp a - clamp b| ≤ |a - b| := by
  unfold clamp
  calc |max 0 (min a 1) - max 0 (min b 1)| = |max (min a 1) 0 - max (min b 1) 0| := by
        rw [max_comm 0, max_comm 0]
    _ ≤ |min a 1 - min b 1| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := by
        have := abs_min_sub_min_le_max a 1 b 1
        simpa using this

lemma clamp_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : clamp u = u := by
  simp [clamp, min_eq_left h1, max_eq_right h0]

lemma pow_lip_unit (d : ℕ) {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    |a ^ d - b ^ d| ≤ d * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun x : ℝ => x ^ d)
    (s := Set.Icc 0 1) (C := d) (fun x _ => (differentiableAt_pow d))
    (fun x hx => by
      rw [(hasDerivAt_pow d x).deriv, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      have : |x ^ (d - 1)| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg hx.1 _)]; exact pow_le_one₀ hx.1 hx.2
      nlinarith [Nat.cast_nonneg (α := ℝ) d, abs_nonneg (x ^ (d - 1))])
    (convex_Icc 0 1) ⟨hb, hb1⟩ ⟨ha, ha1⟩
  simpa [Real.norm_eq_abs] using h

lemma clamp_pow_lip (d : ℕ) (a b : ℝ) :
    |clamp a ^ d - clamp b ^ d| ≤ d * |a - b| :=
  (pow_lip_unit d (clamp_nonneg a) (clamp_le_one a) (clamp_nonneg b) (clamp_le_one b)).trans
    (mul_le_mul_of_nonneg_left (clamp_lip a b) (Nat.cast_nonneg _))

lemma clamp_pow_le (d : ℕ) (hd : 1 ≤ d) (a : ℝ) : |clamp a ^ d| ≤ |a| := by
  rw [abs_of_nonneg (pow_nonneg (clamp_nonneg a) _)]
  calc clamp a ^ d ≤ clamp a := pow_le_of_le_one (clamp_nonneg a) (clamp_le_one a) (by omega)
    _ ≤ |a| := clamp_le_abs a

lemma summable_xs (y : L1) : Summable fun i => |xs y i| := by
  rw [← summable_nat_add_iff 1]; simpa using summable_abs y

/-- Raw clamped drift of coordinate `y i = x (i+1)`. -/
def fr (lam : ℝ) (d : ℕ) (y : L1) (i : ℕ) : ℝ :=
  lam * (clamp (xs y i) ^ d - clamp (xs y (i + 1)) ^ d) - (y i - y (i + 1))

lemma fr_abs_le (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) (i : ℕ) :
    |fr lam d y i| ≤ lam * (|xs y i| + |xs y (i + 1)|) + (|y i| + |y (i + 1)|) := by
  unfold fr
  have h1 := clamp_pow_le d hd (xs y i)
  have h2 := clamp_pow_le d hd (xs y (i + 1))
  have h3 : |clamp (xs y i) ^ d - clamp (xs y (i + 1)) ^ d| ≤ |xs y i| + |xs y (i + 1)| :=
    (abs_sub _ _).trans (add_le_add h1 h2)
  calc |lam * (clamp (xs y i) ^ d - clamp (xs y (i + 1)) ^ d) - (y i - y (i + 1))|
      ≤ |lam * (clamp (xs y i) ^ d - clamp (xs y (i + 1)) ^ d)| + |y i - y (i + 1)| := abs_sub _ _
    _ ≤ lam * (|xs y i| + |xs y (i + 1)|) + (|y i| + |y (i + 1)|) := by
        rw [abs_mul, abs_of_nonneg hlam]
        exact add_le_add (mul_le_mul_of_nonneg_left h3 hlam) (abs_sub _ _)

lemma summable_fr (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) :
    Summable fun i => |fr lam d y i| := by
  refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fr_abs_le lam hlam d hd y) ?_
  have hx := summable_xs y
  have hy := summable_abs y
  exact ((hx.add ((summable_nat_add_iff 1).2 hx)).mul_left lam).add
    (hy.add ((summable_nat_add_iff 1).2 hy))

/-- The clamped drift as a map `ℓ¹ → ℓ¹`. -/
noncomputable def F (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) : L1 :=
  ⟨fr lam d y, memℓp_gen (by simpa [Real.norm_eq_abs] using summable_fr lam hlam d hd y)⟩

@[simp] lemma F_apply (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) (i : ℕ) :
    F lam hlam d hd y i = fr lam d y i := rfl

lemma fr_sub_le (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (y y' : L1) (i : ℕ) :
    |fr lam d y i - fr lam d y' i| ≤
      lam * d * (|xs y i - xs y' i| + |y i - y' i|) + (|y i - y' i| + |y (i+1) - y' (i+1)|) := by
  unfold fr
  have h1 := clamp_pow_lip d (xs y i) (xs y' i)
  have h2 := clamp_pow_lip d (xs y (i + 1)) (xs y' (i + 1))
  simp only [xs_succ] at h2 ⊢
  have e : lam * (clamp (xs y i) ^ d - clamp (y i) ^ d) - (y i - y (i + 1)) -
      (lam * (clamp (xs y' i) ^ d - clamp (y' i) ^ d) - (y' i - y' (i + 1))) =
      lam * ((clamp (xs y i) ^ d - clamp (xs y' i) ^ d) - (clamp (y i) ^ d - clamp (y' i) ^ d))
        - ((y i - y' i) - (y (i+1) - y' (i+1))) := by ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ?_ (abs_sub _ _))
  rw [abs_mul, abs_of_nonneg hlam, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by nlinarith)) hlam

lemma sum_xs_sub (y y' : L1) : ∑' i, |xs y i - xs y' i| = ∑' i, |y i - y' i| := by
  have hs : Summable fun i => |xs y i - xs y' i| := by
    rw [← summable_nat_add_iff 1]; simpa [← lp.coeFn_sub] using summable_abs (y - y')
  rw [hs.tsum_eq_zero_add]; simp

lemma F_lip (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y y' : L1) :
    ‖F lam hlam d hd y - F lam hlam d hd y'‖ ≤ (2 * lam * d + 2) * ‖y - y'‖ := by
  have hδ : Summable fun i => |y i - y' i| := by simpa [← lp.coeFn_sub] using summable_abs (y - y')
  have hxδ : Summable fun i => |xs y i - xs y' i| := by
    rw [← summable_nat_add_iff 1]; simpa using hδ
  have hδ1 : Summable fun i => |y (i+1) - y' (i+1)| := (summable_nat_add_iff 1).2 hδ
  rw [norm_eq, norm_eq]
  simp only [lp.coeFn_sub, Pi.sub_apply, F_apply]
  have hb : Summable fun i =>
      lam * d * (|xs y i - xs y' i| + |y i - y' i|) + (|y i - y' i| + |y (i+1) - y' (i+1)|) :=
    ((hxδ.add hδ).mul_left _).add (hδ.add hδ1)
  calc ∑' i, |fr lam d y i - fr lam d y' i|
      ≤ ∑' i, (lam * d * (|xs y i - xs y' i| + |y i - y' i|) + (|y i - y' i| + |y (i+1) - y' (i+1)|)) :=
        Summable.tsum_le_tsum (fun i => fr_sub_le lam hlam d y y' i)
          (Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => fr_sub_le lam hlam d y y' i) hb) hb
    _ = lam * d * (∑' i, |xs y i - xs y' i| + ∑' i, |y i - y' i|) +
          (∑' i, |y i - y' i| + ∑' i, |y (i+1) - y' (i+1)|) := by
        rw [Summable.tsum_add ((hxδ.add hδ).mul_left _) (hδ.add hδ1), tsum_mul_left,
          Summable.tsum_add hxδ hδ, Summable.tsum_add hδ hδ1]
    _ ≤ (2 * lam * d + 2) * ∑' i, |y i - y' i| := by
        rw [sum_xs_sub]
        have := tsum_shift_le hδ (fun i => abs_nonneg _)
        nlinarith [mul_nonneg hlam (Nat.cast_nonneg (α := ℝ) d)]

lemma F_lipschitz (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) :
    LipschitzWith (Real.toNNReal (2 * lam * d + 2)) (F lam hlam d hd) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  exact F_lip lam hlam d hd y y'

/-! ### The invariant set `K` (= 𝒴 in `y`-coordinates) and the norm bound of `F` on it. -/

def InK (y : L1) : Prop := ∀ i, xs y (i + 1) ≤ xs y i

lemma InK.nonneg {y : L1} (h : InK y) (i : ℕ) : 0 ≤ y i := by
  have hanti : Antitone (fun i => y i) :=
    antitone_nat_of_succ_le (fun i => by simpa using h (i + 1))
  have ht : Tendsto (fun i => y i) atTop (𝓝 0) :=
    squeeze_zero_norm (fun i => le_of_eq (Real.norm_eq_abs _)) (summable_abs y).tendsto_atTop_zero
  exact hanti.le_of_tendsto ht i

lemma InK.xs_mem {y : L1} (h : InK y) (i : ℕ) : 0 ≤ xs y i ∧ xs y i ≤ 1 := by
  have hanti : Antitone (fun i => xs y i) := antitone_nat_of_succ_le h
  refine ⟨?_, ?_⟩
  · cases i with
    | zero => simp
    | succ i => simpa using h.nonneg i
  · simpa using hanti (Nat.zero_le i)

lemma F_norm_le_of_InK (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) {y : L1} (h : InK y) :
    ‖F lam hlam d hd y‖ ≤ lam + 1 := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (by linarith)
  intro s
  simp only [ENNReal.toReal_one, Real.rpow_one, F_apply, Real.norm_eq_abs]
  have hsub := Finset.subset_range_sup_succ s
  set n := s.sup id + 1
  have hterm : ∀ i, |fr lam d y i| ≤ lam * (xs y i ^ d - xs y (i + 1) ^ d) + (y i - y (i + 1)) := by
    intro i
    unfold fr
    rw [clamp_of_mem (h.xs_mem i).1 (h.xs_mem i).2, clamp_of_mem (h.xs_mem (i+1)).1 (h.xs_mem (i+1)).2]
    have h1 : 0 ≤ xs y i ^ d - xs y (i + 1) ^ d :=
      sub_nonneg.2 (pow_le_pow_left₀ (h.xs_mem (i+1)).1 (h i) d)
    have h2 : 0 ≤ y i - y (i + 1) := sub_nonneg.2 (by simpa using h (i + 1))
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg hlam h1), abs_of_nonneg h2]
  calc ∑ i ∈ s, |fr lam d y i| ≤ ∑ i ∈ Finset.range n, |fr lam d y i| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.range n, (lam * (xs y i ^ d - xs y (i + 1) ^ d) + (y i - y (i + 1))) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = lam * (xs y 0 ^ d - xs y n ^ d) + (y 0 - y n) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub' (fun i => xs y i ^ d),
          Finset.sum_range_sub' (fun i => y i)]
    _ ≤ lam + 1 := by
        have a1 : 0 ≤ xs y n ^ d := pow_nonneg (h.xs_mem n).1 d
        have a2 : y 0 ≤ 1 := by simpa using (h.xs_mem 1).2
        have a3 := h.nonneg n
        simp only [xs_zero, one_pow]
        nlinarith

/-! ### Radial truncation: a globally bounded, globally Lipschitz field equal to `F` on `K`. -/

noncomputable def trunc (R : ℝ) (v : L1) : L1 := (R / max R ‖v‖) • v

lemma trunc_norm_le {R : ℝ} (hR : 0 < R) (v : L1) : ‖trunc R v‖ ≤ R := by
  have ha : 0 < max R ‖v‖ := lt_of_lt_of_le hR (le_max_left _ _)
  rw [trunc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ ha]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le

lemma trunc_of_le {R : ℝ} (hR : 0 < R) {v : L1} (hv : ‖v‖ ≤ R) : trunc R v = v := by
  rw [trunc, max_eq_left hv, div_self hR.ne', one_smul]

lemma trunc_lip {R : ℝ} (hR : 0 < R) (u v : L1) : ‖trunc R u - trunc R v‖ ≤ 2 * ‖u - v‖ := by
  set a := max R ‖u‖ with ha_def
  set b := max R ‖v‖ with hb_def
  have ha : R ≤ a := le_max_left _ _
  have hb : R ≤ b := le_max_left _ _
  have ha0 : 0 < a := lt_of_lt_of_le hR ha
  have hb0 : 0 < b := lt_of_lt_of_le hR hb
  have hvb : ‖v‖ ≤ b := le_max_right _ _
  have hab : |a - b| ≤ ‖u - v‖ := by
    calc |a - b| = |max ‖u‖ R - max ‖v‖ R| := by rw [ha_def, hb_def, max_comm R, max_comm R]
      _ ≤ |‖u‖ - ‖v‖| := abs_max_sub_max_le_abs _ _ _
      _ ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
  have e : trunc R u - trunc R v = (R / a) • (u - v) + (R / a - R / b) • v := by
    simp only [trunc, ← ha_def, ← hb_def, smul_sub, sub_smul]; abel
  have h1 : (R / a) * ‖u - v‖ ≤ ‖u - v‖ :=
    mul_le_of_le_one_left (norm_nonneg _) ((div_le_one ha0).2 ha)
  have h2 : |R / a - R / b| * ‖v‖ ≤ ‖u - v‖ := by
    have hne : R / a - R / b = R * (b - a) / (a * b) := by field_simp
    rw [hne, abs_div, abs_mul, abs_of_pos hR, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a,
      div_mul_eq_mul_div, div_le_iff₀ (mul_pos ha0 hb0)]
    have hRv : R * ‖v‖ ≤ a * b := mul_le_mul ha hvb (norm_nonneg v) ha0.le
    have := abs_nonneg (a - b)
    calc R * |a - b| * ‖v‖ = |a - b| * (R * ‖v‖) := by ring
      _ ≤ |a - b| * (a * b) := mul_le_mul_of_nonneg_left hRv this
      _ ≤ ‖u - v‖ * (a * b) := mul_le_mul_of_nonneg_right hab (by positivity)
  rw [e]
  calc ‖(R / a) • (u - v) + (R / a - R / b) • v‖
      ≤ ‖(R / a) • (u - v)‖ + ‖(R / a - R / b) • v‖ := norm_add_le _ _
    _ = (R / a) * ‖u - v‖ + |R / a - R / b| * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ 2 * ‖u - v‖ := by linarith

/-- The globally bounded field. -/
noncomputable def G (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) : L1 :=
  trunc (lam + 1) (F lam hlam d hd y)

lemma G_eq_F (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) {y : L1} (h : InK y) :
    G lam hlam d hd y = F lam hlam d hd y :=
  trunc_of_le (by linarith) (F_norm_le_of_InK lam hlam d hd h)

lemma G_norm_le (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) :
    ‖G lam hlam d hd y‖ ≤ lam + 1 := trunc_norm_le (by linarith) _

lemma G_lipschitz (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) :
    LipschitzWith (Real.toNNReal (2 * (2 * lam * d + 2))) (G lam hlam d hd) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖G lam hlam d hd y - G lam hlam d hd y'‖ ≤ 2 * ‖F lam hlam d hd y - F lam hlam d hd y'‖ :=
        trunc_lip (by linarith) _ _
    _ ≤ 2 * ((2 * lam * d + 2) * ‖y - y'‖) := by
        have := F_lip lam hlam d hd y y'; linarith
    _ = 2 * (2 * lam * d + 2) * ‖y - y'‖ := by ring

/-- Global-in-time existence on `[0, T]` for the truncated field (Picard–Lindelöf). -/
lemma exists_G_sol (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : 0 ≤ T)
    (y0 : L1) : ∃ α : ℝ → L1, α 0 = y0 ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α (G lam hlam d hd (α t)) (Set.Icc 0 T) t := by
  have hP : IsPicardLindelof (fun _ => G lam hlam d hd)
      (t₀ := (⟨0, Set.left_mem_Icc.2 hT⟩ : Set.Icc (0:ℝ) T)) y0
      (Real.toNNReal ((lam + 1) * T)) 0 (Real.toNNReal (lam + 1))
      (Real.toNNReal (2 * (2 * lam * d + 2))) := by
    apply IsPicardLindelof.of_time_independent
    · intro x _
      rw [Real.coe_toNNReal _ (by linarith)]; exact G_norm_le lam hlam d hd x
    · exact (G_lipschitz lam hlam d hd).lipschitzOnWith
    · have : ((Real.toNNReal (lam + 1) : ℝ) * max (T - 0) (0 - 0)) ≤
          (Real.toNNReal ((lam + 1) * T) : ℝ) - ((0 : ℝ≥0) : ℝ) := by
        rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by positivity)]
        simp [max_eq_left hT]
      exact this
  obtain ⟨α, h0, hα⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

lemma nhds_Icc_of_lt {a b t : ℝ} (ha : a ≤ t) (hb : t < b) (s : Set ℝ) (hs : s ⊆ Set.Ici a) :
    Set.Icc a b ∈ 𝓝[s] t :=
  mem_nhdsWithin.2 ⟨Set.Iio b, isOpen_Iio, hb, fun x hx => ⟨hs hx.2, hx.1.le⟩⟩

lemma G_sol_unique (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) {α β : ℝ → L1} {T : ℝ}
    (h0 : α 0 = β 0)
    (hα : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α (G lam hlam d hd (α t)) (Set.Icc 0 T) t)
    (hβ : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt β (G lam hlam d hd (β t)) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc (0:ℝ) T, α t = β t := by
  have key := dist_le_of_trajectories_ODE (v := fun _ => G lam hlam d hd) (δ := 0)
    (fun _ => G_lipschitz lam hlam d hd)
    (fun t ht => (hα t ht).continuousWithinAt)
    (fun t ht => (hα t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (nhds_Icc_of_lt ht.1 ht.2 _ (fun x hx => le_trans ht.1 hx)))
    (fun t ht => (hβ t ht).continuousWithinAt)
    (fun t ht => (hβ t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (nhds_Icc_of_lt ht.1 ht.2 _ (fun x hx => le_trans ht.1 hx)))
    (by rw [h0, dist_self])
  intro t ht
  have := key t ht
  rw [zero_mul] at this
  exact dist_le_zero.1 this

/-- Global solution on `[0, ∞)` of the truncated system. -/
lemma exists_G_global (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y0 : L1) :
    ∃ α : ℝ → L1, α 0 = y0 ∧
      ∀ t, 0 ≤ t → HasDerivWithinAt α (G lam hlam d hd (α t)) (Set.Ici 0) t := by
  choose sol hsol0 hsol using fun n : ℕ =>
    exists_G_sol lam hlam d hd ((n:ℝ) + 1) (by positivity) y0
  have agree : ∀ m n : ℕ, m ≤ n → ∀ u ∈ Set.Icc (0:ℝ) ((m:ℝ) + 1), sol m u = sol n u := by
    intro m n hmn
    have hsub : Set.Icc (0:ℝ) ((m:ℝ) + 1) ⊆ Set.Icc 0 ((n:ℝ) + 1) :=
      Set.Icc_subset_Icc le_rfl (by exact_mod_cast Nat.add_le_add_right hmn 1)
    refine G_sol_unique lam hlam d hd (by rw [hsol0, hsol0]) (fun t ht => hsol m t ht)
      (fun t ht => ((hsol n t (hsub ht)).mono hsub))
  refine ⟨fun t => sol ⌊t⌋₊ t, by simp [hsol0], fun t ht => ?_⟩
  set n := ⌊t⌋₊
  have htn : t < (n:ℝ) + 1 := Nat.lt_floor_add_one t
  have hmem : Set.Icc (0:ℝ) ((n:ℝ) + 1) ∈ 𝓝[Set.Ici 0] t :=
    nhds_Icc_of_lt ht htn _ (fun x hx => hx)
  have heq : ∀ u ∈ Set.Icc (0:ℝ) ((n:ℝ) + 1), sol ⌊u⌋₊ u = sol n u := by
    intro u hu
    rcases le_total ⌊u⌋₊ n with h | h
    · exact agree _ _ h u ⟨hu.1, (Nat.lt_floor_add_one u).le⟩
    · exact (agree _ _ h u hu).symm
  have hd' := ((hsol n t ⟨ht, htn.le⟩).mono_of_mem_nhdsWithin hmem)
  show HasDerivWithinAt (fun t => sol ⌊t⌋₊ t) (G lam hlam d hd (sol n t)) (Set.Ici 0) t
  exact hd'.congr_of_eventuallyEq (Filter.mem_of_superset hmem heq) (heq t ⟨ht, htn.le⟩)

/-! ### Invariance of `K` under the `G`-flow. -/

def pp (y : L1) (i : ℕ) : ℝ := xs y i - xs y (i + 1)

def dpp (v : L1) (i : ℕ) : ℝ := (if i = 0 then 0 else v (i - 1)) - v i

lemma pp_eq (y : L1) (i : ℕ) : pp y i = (if i = 0 then 1 else y (i - 1)) - y i := by
  simp [pp, xs]

lemma hasDerivWithinAt_coord {α : ℝ → L1} {v : L1} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α v s t) (j : ℕ) :
    HasDerivWithinAt (fun u => α u j) (v j) s t := by
  have := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 j).hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [Function.comp_def, lp.evalCLM] using this

lemma hasDerivWithinAt_pp {α : ℝ → L1} {v : L1} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α v s t) (i : ℕ) :
    HasDerivWithinAt (fun u => pp (α u) i) (dpp v i) s t := by
  have hi := hasDerivWithinAt_coord h i
  simp only [pp_eq, dpp]
  by_cases h0 : i = 0
  · simp only [h0, if_true]
    subst h0
    simpa using hi.const_sub 1
  · simp only [h0, if_false]
    exact (hasDerivWithinAt_coord h (i - 1)).sub hi

lemma G_eq_smul (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ G lam hlam d hd y = θ • F lam hlam d hd y := by
  have hm : 0 < max (lam + 1) ‖F lam hlam d hd y‖ :=
    lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨(lam + 1) / max (lam + 1) ‖F lam hlam d hd y‖, div_nonneg (by linarith) hm.le, ?_, rfl⟩
  exact (div_le_one hm).2 (le_max_left _ _)

lemma clamp_mono {a b : ℝ} (h : a ≤ b) : clamp a ≤ clamp b :=
  max_le_max le_rfl (min_le_min h le_rfl)

lemma gdiff_lower (d : ℕ) {a b B : ℝ} (hB : 0 ≤ B) (h : -B ≤ a - b) :
    -(d * B) ≤ clamp a ^ d - clamp b ^ d := by
  rcases le_total b a with hab | hab
  · have : clamp b ^ d ≤ clamp a ^ d := pow_le_pow_left₀ (clamp_nonneg b) (clamp_mono hab) d
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hB]
  · have h1 := (abs_le.1 (clamp_pow_lip d a b)).1
    have h2 : |a - b| ≤ B := by rw [abs_of_nonpos (by linarith)]; linarith
    linarith [mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) d)]

lemma gdiff_pos (d : ℕ) {a b : ℝ} (h : 0 ≤ a - b) :
    0 ≤ clamp a ^ d - clamp b ^ d ∧ clamp a ^ d - clamp b ^ d ≤ d * (a - b) := by
  refine ⟨sub_nonneg.2 (pow_le_pow_left₀ (clamp_nonneg b) (clamp_mono (by linarith)) d), ?_⟩
  have h1 := (abs_le.1 (clamp_pow_lip d a b)).2
  rwa [abs_of_nonneg h] at h1

lemma gdiff_neg (d : ℕ) {a b : ℝ} (h : a - b < 0) : clamp a ^ d - clamp b ^ d ≤ 0 :=
  sub_nonpos.2 (pow_le_pow_left₀ (clamp_nonneg a) (clamp_mono (by linarith)) d)

lemma arith_core {lam dd θ ι B a b N e2 : ℝ} (hlam : 0 ≤ lam) (hdd : 0 ≤ dd) (hB : 0 ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hι0 : 0 ≤ ι) (hι1 : ι ≤ 1)
    (ha : -B ≤ a) (hb : -B ≤ b) (hN : -(lam * dd * B) ≤ N)
    (he_pos : 0 ≤ a → 0 ≤ e2 ∧ e2 ≤ dd * a) (he_neg : a < 0 → e2 ≤ 0) :
    -(2 * (lam * dd + 1) * B) ≤ (lam * dd + 1) * a + θ * (N - ι * a - lam * e2 + b) := by
  have hld : 0 ≤ lam * dd := mul_nonneg hlam hdd
  have h1 : -(lam * dd * B) ≤ θ * N := by
    nlinarith [mul_nonneg hθ0 (show 0 ≤ N + lam * dd * B by linarith),
      mul_nonneg (sub_nonneg.2 hθ1) (mul_nonneg hld hB)]
  have h2 : -B ≤ θ * b := by
    nlinarith [mul_nonneg hθ0 (show 0 ≤ b + B by linarith), mul_nonneg (sub_nonneg.2 hθ1) hB]
  have h3 : -((lam * dd + 1) * B) ≤ (lam * dd + 1) * a - θ * ι * a - θ * lam * e2 := by
    rcases le_or_gt 0 a with ha0 | ha0
    · obtain ⟨he1, he2⟩ := he_pos ha0
      have hθι : θ * ι ≤ 1 := by nlinarith
      have q1 : θ * ι * a ≤ a := by nlinarith [mul_nonneg hθ0 hι0]
      have q2 : θ * lam * e2 ≤ lam * e2 := by nlinarith [mul_nonneg hlam he1]
      have q3 : lam * e2 ≤ lam * (dd * a) := mul_le_mul_of_nonneg_left he2 hlam
      nlinarith [mul_nonneg hld hB, mul_nonneg hld ha0]
    · have he := he_neg ha0
      have q1 : 0 ≤ -(θ * ι * a) := by nlinarith [mul_nonneg hθ0 hι0]
      have q2 : 0 ≤ -(θ * lam * e2) := by nlinarith [mul_nonneg hθ0 hlam]
      nlinarith [mul_le_mul_of_nonneg_left ha (show 0 ≤ lam * dd + 1 by linarith)]
  nlinarith

lemma key_ineq (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) (y : L1) {B : ℝ} (hB : 0 ≤ B)
    (hy : ∀ j, -B ≤ pp y j) (i : ℕ) :
    -(2 * (lam * d + 1) * B) ≤ (lam * d + 1) * pp y i + dpp (G lam hlam d hd y) i := by
  obtain ⟨θ, hθ0, hθ1, hG⟩ := G_eq_smul lam hlam d hd y
  have hdd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  cases i with
  | zero =>
    have hE : (lam * d + 1) * pp y 0 + dpp (G lam hlam d hd y) 0 =
        (lam * d + 1) * pp y 0 + θ * (0 - 0 * pp y 0 -
          lam * (clamp (xs y 0) ^ d - clamp (xs y (0 + 1)) ^ d) + pp y (0 + 1)) := by
      rw [hG]; simp [dpp, pp, fr, xs]; ring
    rw [hE]
    exact arith_core hlam hdd hB hθ0 hθ1 le_rfl zero_le_one (hy 0) (hy 1) (by nlinarith [mul_nonneg (mul_nonneg hlam hdd) hB])
      (fun h => gdiff_pos d h) (fun h => gdiff_neg d h)
  | succ k =>
    have hE : (lam * d + 1) * pp y (k + 1) + dpp (G lam hlam d hd y) (k + 1) =
        (lam * d + 1) * pp y (k + 1) + θ * (lam * (clamp (xs y k) ^ d - clamp (xs y (k + 1)) ^ d)
          - 1 * pp y (k + 1) - lam * (clamp (xs y (k + 1)) ^ d - clamp (xs y (k + 1 + 1)) ^ d)
          + pp y (k + 1 + 1)) := by
      rw [hG]; simp [dpp, pp, fr, xs]; ring
    rw [hE]
    have hN : -(lam * d * B) ≤ lam * (clamp (xs y k) ^ d - clamp (xs y (k + 1)) ^ d) := by
      have := mul_le_mul_of_nonneg_left (gdiff_lower d hB (hy k)) hlam
      linarith
    exact arith_core hlam hdd hB hθ0 hθ1 zero_le_one le_rfl (hy (k + 1)) (hy (k + 2)) hN
      (fun h => gdiff_pos d h) (fun h => gdiff_neg d h)

lemma abs_apply_le (y : L1) (j : ℕ) : |y j| ≤ ‖y‖ := by
  simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num : (1:ℝ≥0∞) ≠ 0) y j

lemma pp_ge (y : L1) (j : ℕ) : -(1 + 2 * ‖y‖) ≤ pp y j := by
  have h1 : -‖y‖ - 1 ≤ xs y j := by
    cases j with
    | zero => simp; linarith [norm_nonneg y]
    | succ k => simp only [xs_succ]; linarith [abs_apply_le y k, neg_abs_le (y k)]
  simp only [pp, xs_succ]
  linarith [abs_apply_le y j, le_abs_self (y j), norm_nonneg y]

/-- One time step of length `h` preserves `K`. -/
lemma step (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) {α : ℝ → L1}
    (hα : ∀ t, 0 ≤ t → HasDerivWithinAt α (G lam hlam d hd (α t)) (Set.Ici 0) t)
    {s h : ℝ} (hs : 0 ≤ s) (hh0 : 0 ≤ h)
    (hh : h * Real.exp ((lam * d + 1) * h) * (2 * (lam * d + 1)) ≤ 1 / 2)
    (hK : InK (α s)) : ∀ τ ∈ Set.Icc s (s + h), InK (α τ) := by
  set c : ℝ := lam * d + 1 with hc_def
  have hc0 : 0 ≤ c := by have := mul_nonneg hlam (Nat.cast_nonneg (α := ℝ) d); linarith
  have hsub : Set.Icc s (s + h) ⊆ Set.Ici 0 := fun x hx => hs.trans hx.1
  have cont : ContinuousOn α (Set.Icc s (s + h)) := fun t ht =>
    (hα t (hs.trans ht.1)).continuousWithinAt.mono hsub
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn cont
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR s ⟨le_rfl, by linarith⟩)
  set B0 : ℝ := 1 + 2 * R
  have hB0 : 0 ≤ B0 := by positivity
  have claim : ∀ n : ℕ, ∀ τ ∈ Set.Icc s (s + h), ∀ j, -(B0 * (1 / 2) ^ n) ≤ pp (α τ) j := by
    intro n
    induction n with
    | zero =>
      intro τ hτ j
      have := pp_ge (α τ) j
      have := hR τ hτ
      simp only [pow_zero, mul_one]; linarith
    | succ n ih =>
      intro τ hτ i
      set B : ℝ := B0 * (1 / 2) ^ n with hB_def
      have hB : 0 ≤ B := by positivity
      set C : ℝ := Real.exp (c * (s + h)) * (2 * c) * B
      set f : ℝ → ℝ := fun u => -(Real.exp (c * u) * pp (α u) i)
      set f' : ℝ → ℝ := fun u =>
        -(Real.exp (c * u) * (c * 1) * pp (α u) i + Real.exp (c * u) * dpp (G lam hlam d hd (α u)) i)
      have hf_der : ∀ u, 0 ≤ u → HasDerivWithinAt f (f' u) (Set.Ici 0) u := by
        intro u hu
        have h1 := ((hasDerivAt_id' u).const_mul c).exp.hasDerivWithinAt (s := Set.Ici 0)
        exact (h1.mul (hasDerivWithinAt_pp (hα u hu) i)).neg
      have hτs : Set.Icc s τ ⊆ Set.Icc s (s + h) := Set.Icc_subset_Icc le_rfl hτ.2
      have hle := image_le_of_deriv_right_le_deriv_boundary (a := s) (b := τ) (f := f) (f' := f')
        (B := fun u => -(Real.exp (c * s) * pp (α s) i) + C * (u - s)) (B' := fun _ => C * 1)
        (fun u hu => (hf_der u (hs.trans hu.1)).continuousWithinAt.mono
          (fun x hx => hs.trans hx.1))
        (fun u hu => (hf_der u (hs.trans hu.1)).mono (Set.Ici_subset_Ici.2 (hs.trans hu.1)))
        (by simp [f]) (by fun_prop)
        (fun u _ => (((hasDerivAt_id' u).sub_const s).const_mul C).const_add _ |>.hasDerivWithinAt)
        (fun u hu => by
          have hu' : u ∈ Set.Icc s (s + h) := hτs (Set.Ico_subset_Icc_self hu)
          have hk := key_ineq lam hlam d hd (α u) hB (ih u hu') i
          have he1 : Real.exp (c * u) ≤ Real.exp (c * (s + h)) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hu'.2 hc0)
          have hep := Real.exp_pos (c * u)
          have hKB : 0 ≤ 2 * c * B := by positivity
          simp only [f', C]
          nlinarith [mul_le_mul_of_nonneg_left hk hep.le, mul_le_mul_of_nonneg_right he1 hKB])
        ⟨hτ.1, le_rfl⟩
      simp only [f] at hle
      have hps : 0 ≤ pp (α s) i := by simpa [pp] using hK i
      have hes := Real.exp_pos (c * s)
      have hτ1 : τ - s ≤ h := by linarith [hτ.2]
      have hτ0 : 0 ≤ τ - s := by linarith [hτ.1]
      have hC0 : 0 ≤ C := by positivity
      have h2 : -(C * h) ≤ Real.exp (c * τ) * pp (α τ) i := by
        nlinarith [mul_nonneg hes.le hps, mul_le_mul_of_nonneg_left hτ1 hC0]
      have hsplit : Real.exp (c * (s + h)) = Real.exp (c * τ) * Real.exp (c * (s + h) - c * τ) := by
        rw [← Real.exp_add]; ring_nf
      have hX : Real.exp (c * (s + h) - c * τ) ≤ Real.exp (c * h) :=
        Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hτ.1 hc0])
      set X := Real.exp (c * (s + h) - c * τ)
      have heτ := Real.exp_pos (c * τ)
      have h3 : 0 ≤ Real.exp (c * τ) * (pp (α τ) i + X * (2 * c) * B * h) := by
        have : C * h = Real.exp (c * τ) * (X * (2 * c) * B * h) := by
          simp only [C]; rw [hsplit]; ring
        nlinarith
      have h4 : 0 ≤ pp (α τ) i + X * (2 * c) * B * h :=
        (mul_nonneg_iff_of_pos_left heτ).1 h3
      have h5 : X * (2 * c) * B * h ≤ B / 2 := by
        have : X * h * (2 * c) ≤ 1 / 2 := by
          have := mul_le_mul_of_nonneg_right hX (show 0 ≤ h * (2 * c) by positivity)
          nlinarith
        nlinarith
      have : B0 * (1 / 2) ^ (n + 1) = B / 2 := by simp only [B, pow_succ]; ring
      rw [this]; linarith
  intro τ hτ
  have hpos : ∀ j, 0 ≤ pp (α τ) j := by
    intro j
    have ht : Tendsto (fun n : ℕ => -(B0 * (1 / 2) ^ n)) atTop (𝓝 (-(B0 * 0))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul B0).neg
    simpa using le_of_tendsto' ht (fun n => claim n τ hτ j)
  intro j
  have := hpos j
  simp only [pp] at this
  linarith

lemma invariant (lam : ℝ) (hlam : 0 ≤ lam) (d : ℕ) (hd : 1 ≤ d) {α : ℝ → L1}
    (hα : ∀ t, 0 ≤ t → HasDerivWithinAt α (G lam hlam d hd (α t)) (Set.Ici 0) t)
    (h0 : InK (α 0)) : ∀ t, 0 ≤ t → InK (α t) := by
  set c : ℝ := lam * d + 1 with hc_def
  have hc : 1 ≤ c := by have := mul_nonneg hlam (Nat.cast_nonneg (α := ℝ) d); linarith
  have he : 1 ≤ Real.exp c := Real.one_le_exp (by linarith)
  have hD : 0 < 2 * (2 * c) * Real.exp c := by positivity
  set h : ℝ := 1 / (2 * (2 * c) * Real.exp c) with hh_def
  have hh0 : 0 < h := by positivity
  have h_le1 : h ≤ 1 := by rw [hh_def, div_le_one hD]; nlinarith
  have hexp : Real.exp (c * h) ≤ Real.exp c := Real.exp_le_exp.2 (by nlinarith)
  have hh : h * Real.exp (c * h) * (2 * c) ≤ 1 / 2 := by
    calc h * Real.exp (c * h) * (2 * c) ≤ h * Real.exp c * (2 * c) := by gcongr
      _ = 1 / 2 := by rw [hh_def]; field_simp
  have key : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) (k * h), InK (α τ) := by
    intro k
    induction k with
    | zero =>
      intro τ hτ
      have : τ = 0 := le_antisymm (by simpa using hτ.2) hτ.1
      rw [this]; exact h0
    | succ k ih =>
      intro τ hτ
      rcases le_total τ (k * h) with h1 | h1
      · exact ih τ ⟨hτ.1, h1⟩
      · exact step lam hlam d hd hα (s := k * h) (by positivity) hh0.le hh
          (ih _ ⟨by positivity, le_rfl⟩) τ ⟨h1, by push_cast at hτ; linarith [hτ.2]⟩
  intro t ht
  obtain ⟨k, hk⟩ := exists_nat_ge (t / h)
  exact key k t ⟨ht, by rw [div_le_iff₀ hh0] at hk; linarith⟩

open StrictCompatLB.MeanField in
theorem k7 : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d → ∀ q₀ : ℕ → ℝ, InY q₀ →
    ∃ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s ∧
      (∀ t : ℝ, 0 ≤ t → InY (s t)) ∧ s 0 = q₀ := by
  intro lam hlam0 _ d hd2 q₀ hq
  have hlam : 0 ≤ lam := hlam0.le
  have hd : 1 ≤ d := by omega
  obtain ⟨⟨hq0, hqnn, hqanti⟩, hqs⟩ := hq
  have habs : ∀ i, |q₀ (i + 1)| = q₀ (i + 1) := fun i => abs_of_nonneg (hqnn (i + 1))
  let y0 : L1 := ⟨fun i => q₀ (i + 1),
    memℓp_gen (by simpa [Real.norm_eq_abs, habs] using hqs)⟩
  have hxs0 : ∀ i, xs y0 i = q₀ i := by
    intro i
    cases i with
    | zero => simp [hq0]
    | succ k => simp only [xs_succ]; rfl
  have hK0 : InK y0 := fun i => by rw [hxs0, hxs0]; exact hqanti (Nat.le_succ i)
  obtain ⟨α, hα0, hα⟩ := exists_G_global lam hlam d hd y0
  have hinv := invariant lam hlam d hd hα (by rw [hα0]; exact hK0)
  have hstate : ∀ t, 0 ≤ t → PowerTwoChoices.Limit.IsState (xs (α t)) := fun t ht =>
    ⟨xs_zero _, fun i => ((hinv t ht).xs_mem i).1, antitone_nat_of_succ_le (hinv t ht)⟩
  refine ⟨fun t => xs (α t), ⟨hstate, ?_⟩, fun t ht => ⟨hstate t ht, ?_⟩, ?_⟩
  · intro i hi t ht
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hder := hasDerivWithinAt_coord (hα t ht) k
    rw [G_eq_F lam hlam d hd (hinv t ht), F_apply] at hder
    have hm := (hinv t ht).xs_mem
    convert hder using 1
    · funext u; simp
    · simp only [PowerTwoChoices.Limit.drift, fr]
      rw [clamp_of_mem (hm k).1 (hm k).2, clamp_of_mem (hm (k + 1)).1 (hm (k + 1)).2]
      simp
  · simpa using (summable_abs (α t)).of_abs
  · funext i
    show xs (α 0) i = q₀ i
    rw [hα0, hxs0]

end SC77K7

open StrictCompatLB.MeanField in
theorem solution : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d → ∀ q₀ : ℕ → ℝ, InY q₀ →
    ∃ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s ∧
      (∀ t : ℝ, 0 ≤ t → InY (s t)) ∧ s 0 = q₀ := by
  exact SC77K7.k7
