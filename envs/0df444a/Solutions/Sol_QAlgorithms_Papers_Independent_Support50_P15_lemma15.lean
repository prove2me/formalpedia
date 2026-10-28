-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P15.lemma15
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:02:04.631981+00:00
-- url     : https://prove2.me/submissions/ee1e23f4-4a06-4b4e-be14-ce1227c54b24

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

open Real Set

namespace X8L15

lemma two_log_lt {x : ℝ} (hx : 1 < x) : 2 * Real.log x < x - x⁻¹ := by
  have h := (Real.self_lt_sinh_iff (x := Real.log x)).2 (Real.log_pos hx)
  rw [Real.sinh_log (by linarith)] at h; linarith

lemma cosh_lb (y : ℝ) : 1 + y ^ 2 / 2 + y ^ 4 / 24 ≤ Real.cosh y := by
  have h := Real.hasSum_cosh y
  have := sum_le_hasSum (Finset.range 3) (fun i _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)) h
  simp [Finset.sum_range_succ, Nat.factorial] at this
  norm_num at this ⊢
  linarith

lemma lt_log_two_cosh {y : ℝ} : y < Real.log 2 * Real.cosh y := by
  have hc := cosh_lb y
  have hl := Real.log_two_gt_d9
  have h1 : y < 0.6931471803 * (1 + y ^ 2 / 2 + y ^ 4 / 24) := by
    nlinarith [sq_nonneg (y ^ 2 - 1.44), sq_nonneg (y - 1.163), sq_nonneg y]
  have h2 : 0.6931471803 * (1 + y ^ 2 / 2 + y ^ 4 / 24) ≤ Real.log 2 * Real.cosh y := by
    apply mul_le_mul hl.le hc (by positivity) (by linarith)
  linarith

lemma sq_bound1 {s q : ℝ} (hs : 0 < s) (hsq : s < q) :
    s * q * (2 * Real.log (q / s)) < q ^ 2 - s ^ 2 := by
  have hx : 1 < q / s := by rw [one_lt_div hs]; exact hsq
  have h := two_log_lt hx
  have hq : 0 < q := hs.trans hsq
  have e : s * q * (q / s - (q / s)⁻¹) = q ^ 2 - s ^ 2 := by
    field_simp
  rw [← e]
  exact mul_lt_mul_of_pos_left h (by positivity)

lemma sq_bound2 {s q : ℝ} (hs : 0 < s) (hsq : s < q) :
    s * q * (2 * Real.log (q / s)) < Real.log 2 * (q ^ 2 + s ^ 2) := by
  have hq : 0 < q := hs.trans hsq
  have h := lt_log_two_cosh (y := Real.log (q / s))
  rw [Real.cosh_log (by positivity)] at h
  have e : s * q * (2 * (Real.log 2 * ((q / s + (q / s)⁻¹) / 2))) = Real.log 2 * (q ^ 2 + s ^ 2) := by
    field_simp
  rw [← e]
  apply mul_lt_mul_of_pos_left (by linarith) (by positivity)

/-- data for `r ∈ (0,1/2)`. -/
lemma ell_eq {k r : ℝ} (hk : 0 < k) (h0 : 0 < r) (h1 : r < 1 / 2) :
    ∃ s q : ℝ, 0 < s ∧ s < q ∧ s ^ 2 = r ∧ q ^ 2 = 1 - r ∧
      Real.log ((1 - r) / r * k) = 2 * Real.log (q / s) + Real.log k := by
  refine ⟨√r, √(1 - r), Real.sqrt_pos.2 h0, Real.sqrt_lt_sqrt h0.le (by linarith),
    Real.sq_sqrt h0.le, Real.sq_sqrt (by linarith), ?_⟩
  have hs := Real.sqrt_pos.2 h0
  have hq : 0 < √(1 - r) := Real.sqrt_pos.2 (by linarith)
  have : (1 - r) / r * k = (√(1 - r) / √r) ^ 2 * k := by
    rw [div_pow, Real.sq_sqrt h0.le, Real.sq_sqrt (by linarith)]
  rw [this, Real.log_mul (by positivity) hk.ne', Real.log_pow]; push_cast; ring

lemma pw_easy {k r : ℝ} (hk : 1 ≤ k) (h0 : 0 < r) (h1 : r < 1 / 2) :
    r * (1 - r) * (Real.log ((1 - r) / r * k)) ^ 2 < (Real.log k) ^ 2 / 4 + 1 := by
  obtain ⟨s, q, hs, hsq, hs2, hq2, he⟩ := ell_eq (k := k) (by linarith) h0 h1
  rw [he]
  set l := 2 * Real.log (q / s) with hl
  set c := Real.log k
  have hc : 0 ≤ c := Real.log_nonneg hk
  have hq : 0 < q := hs.trans hsq
  have hlpos : 0 < l := by
    have : 1 < q / s := by rw [one_lt_div hs]; exact hsq
    have := Real.log_pos this; linarith
  have hb := sq_bound1 hs hsq
  rw [← hl] at hb
  set a := r * (1 - r) with ha
  have ha' : a = (s * q) ^ 2 := by rw [ha, mul_pow, hs2, hq2]
  set t := 1 / 2 - r with ht
  have htpos : 0 < t := by linarith
  have hA : a * l ^ 2 < 4 * t ^ 2 := by
    have h2 : 0 ≤ s * q * l := by positivity
    have : (s * q * l) ^ 2 < (q ^ 2 - s ^ 2) ^ 2 := by
      apply pow_lt_pow_left₀ hb h2 (by norm_num)
    rw [ha']; nlinarith
  have hat : a = 1 / 4 - t ^ 2 := by rw [ha, ht]; ring
  have e1 : a * (l + c) ^ 2 - c ^ 2 / 4 = a * l ^ 2 + 2 * a * c * l - c ^ 2 * t ^ 2 := by
    rw [hat]; ring
  have e2 : t ^ 2 * (2 * a * c * l) ≤ c ^ 2 * t ^ 4 + a ^ 2 * l ^ 2 := by
    nlinarith [sq_nonneg (c * t ^ 2 - a * l)]
  have e3 : t ^ 2 * (a * (l + c) ^ 2 - c ^ 2 / 4) < t ^ 2 := by
    rw [e1]
    have : t ^ 2 * (a * l ^ 2 + 2 * a * c * l - c ^ 2 * t ^ 2) ≤ a * l ^ 2 * (t ^ 2 + a) := by
      nlinarith
    have h4 : a * l ^ 2 * (t ^ 2 + a) = a * l ^ 2 / 4 := by rw [hat]; ring
    nlinarith
  have : a * (l + c) ^ 2 - c ^ 2 / 4 < 1 := by
    by_contra hcon; push Not at hcon
    nlinarith [mul_le_mul_of_nonneg_left hcon (sq_nonneg t)]
  linarith

lemma pw_two {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) :
    r * (1 - r) * (Real.log ((1 - r) / r * 1)) ^ 2 < (Real.log 2) ^ 2 := by
  obtain ⟨s, q, hs, hsq, hs2, hq2, he⟩ := ell_eq (k := 1) one_pos h0 h1
  rw [he, Real.log_one, add_zero]
  have hb := sq_bound2 hs hsq
  have hq : 0 < q := hs.trans hsq
  have hlpos : 0 < Real.log (q / s) := Real.log_pos (by rw [one_lt_div hs]; exact hsq)
  have hsum : q ^ 2 + s ^ 2 = 1 := by rw [hs2, hq2]; ring
  rw [hsum, mul_one] at hb
  have h2 : 0 ≤ s * q * (2 * Real.log (q / s)) := by positivity
  have := pow_lt_pow_left₀ hb h2 (by norm_num : (2 : ℕ) ≠ 0)
  have e : r * (1 - r) * (2 * Real.log (q / s)) ^ 2 = (s * q * (2 * Real.log (q / s))) ^ 2 := by
    have : (s * q * (2 * Real.log (q / s))) ^ 2 = s ^ 2 * q ^ 2 * (2 * Real.log (q / s)) ^ 2 := by ring
    rw [this, hs2, hq2]
  rw [e]; exact this

lemma pw_low {k : ℝ} (hk : 1 ≤ k) :
    ∃ r ∈ Ioo (0 : ℝ) (1 / 2), (Real.log k) ^ 2 / 4 < r * (1 - r) * (Real.log ((1 - r) / r * k)) ^ 2 := by
  set c := Real.log k
  have hc : 0 ≤ c := Real.log_nonneg hk
  set t := 1 / (c + 4) with ht
  have htpos : 0 < t := by positivity
  have htc : (c + 4) * t = 1 := by rw [ht]; field_simp
  have ht4 : t ≤ 1 / 4 := by nlinarith
  refine ⟨1 / 2 - t, ⟨by linarith, by linarith⟩, ?_⟩
  set r := 1 / 2 - t with hr
  have h0 : 0 < r := by linarith
  have h1 : r < 1 / 2 := by linarith
  obtain ⟨s, q, hs, hsq, hs2, hq2, he⟩ := ell_eq (by linarith) h0 h1
  set l := Real.log ((1 - r) / r)
  have hle : Real.log ((1 - r) / r * k) = l + c := by
    rw [Real.log_mul (by apply ne_of_gt; apply div_pos <;> linarith) (by linarith)]
  rw [hle]
  have hl1 : 1 - ((1 - r) / r)⁻¹ ≤ l := Real.one_sub_inv_le_log_of_pos (by apply div_pos <;> linarith)
  have hinv : ((1 - r) / r)⁻¹ = r / (1 - r) := inv_div _ _
  rw [hinv] at hl1
  have h1r : 0 < 1 - r := by linarith
  have hl2 : (1 - r) * l ≥ 1 - 2 * r := by
    have : (1 - r) * (1 - r / (1 - r)) = 1 - 2 * r := by field_simp; ring
    nlinarith
  have hlpos : 0 < l := by
    by_contra hh; push Not at hh; nlinarith
  set a := r * (1 - r)
  have hapos : 0 < a := by positivity
  have hkey : 2 * a * l - c * t ^ 2 ≥ 0 := by
    have : 2 * a * l ≥ 2 * r * (1 - 2 * r) := by
      have := mul_le_mul_of_nonneg_left hl2 (by linarith : (0 : ℝ) ≤ 2 * r)
      nlinarith
    have e : 2 * r * (1 - 2 * r) - c * t ^ 2 = t * (2 - (c + 4) * t) := by rw [hr]; ring
    nlinarith
  have e1 : a * (l + c) ^ 2 - c ^ 2 / 4 = a * l ^ 2 + c * (2 * a * l - c * t ^ 2) := by
    simp only [a, hr]; ring
  have : 0 < a * l ^ 2 := by positivity
  nlinarith [mul_nonneg hc hkey]

end X8L15


open Real Set

namespace X8L15

open QAlgorithms.Papers.Independent.Support50.P15

lemma vo_eq {k r : ℝ} (hk : 0 < k) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    r * (1 - r) * (Real.log ((1 - r) / r * k)) ^ 2 =
      (1 - r) * (r * (Real.log ((1 - r) * k)) ^ 2 - 2 * Real.log ((1 - r) * k) * (r * Real.log r)
        + 4 * (√r * Real.log √r) ^ 2) := by
  rcases hr0.eq_or_lt with h | h
  · subst h; simp
  · have e : (1 - r) / r * k = (1 - r) * k / r := by ring
    rw [e, Real.log_div (by have : 0 < 1 - r := by linarith
                            positivity) h.ne', Real.log_sqrt h.le, mul_pow, Real.sq_sqrt h.le]
    ring

lemma vo_cont {k : ℝ} (hk : 0 < k) :
    ContinuousOn (fun r : ℝ => r * (1 - r) * (Real.log ((1 - r) / r * k)) ^ 2) (Icc 0 (1 / 2)) := by
  have hL : ContinuousOn (fun r : ℝ => Real.log ((1 - r) * k)) (Icc 0 (1 / 2)) := by
    apply ContinuousOn.log (by fun_prop)
    intro r hr; have : 0 < 1 - r := by linarith [hr.2]
    positivity
  have hm : Continuous (fun r : ℝ => r * Real.log r) := Real.continuous_mul_log
  have hm2 : Continuous (fun r : ℝ => √r * Real.log √r) :=
    Real.continuous_mul_log.comp Real.continuous_sqrt
  have hG : ContinuousOn (fun r : ℝ => (1 - r) * (r * (Real.log ((1 - r) * k)) ^ 2
      - 2 * Real.log ((1 - r) * k) * (r * Real.log r) + 4 * (√r * Real.log √r) ^ 2)) (Icc 0 (1 / 2)) := by
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.add
    · apply ContinuousOn.sub
      · exact continuousOn_id.mul (hL.pow 2)
      · exact (continuousOn_const.mul hL).mul hm.continuousOn
    · exact continuousOn_const.mul (hm2.continuousOn.pow 2)
  exact hG.congr (fun r hr => vo_eq hk hr.1 hr.2)

lemma sup_lt {f : ℝ → ℝ} {B : ℝ} (hf : ContinuousOn f (Icc 0 (1 / 2)))
    (hB : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f r < B) : sSup (f '' Ioo 0 (1 / 2)) < B := by
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by norm_num)) hf
  have hne : (f '' Ioo (0 : ℝ) (1 / 2)).Nonempty := ⟨f (1 / 4), 1 / 4, ⟨by norm_num, by norm_num⟩, rfl⟩
  have : sSup (f '' Ioo 0 (1 / 2)) ≤ f m := by
    apply csSup_le hne
    rintro _ ⟨r, hr, rfl⟩
    exact hmax ⟨hr.1.le, hr.2.le⟩
  exact this.trans_lt (hB m hm)

lemma vo_fun (d : ℕ) : varianceObjective d =
    fun r : ℝ => r * (1 - r) * (Real.log ((1 - r) / r * ((d : ℝ) - 1))) ^ 2 := by
  funext r; rfl

lemma max_lt_easy {d : ℕ} (hd : 2 ≤ d) : maxVariance d < easyVariance d := by
  have hk : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold maxVariance easyVariance
  rw [vo_fun]
  apply sup_lt (vo_cont (by linarith))
  intro r hr
  rcases hr.1.eq_or_lt with h | h
  · subst h; simp; positivity
  rcases hr.2.eq_or_lt with h' | h'
  · subst h'; norm_num; linarith
  exact pw_easy hk h h'

lemma max_lt_two : maxVariance 2 < (Real.log 2) ^ 2 := by
  unfold maxVariance
  rw [vo_fun]
  apply sup_lt (vo_cont (by norm_num))
  intro r hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases hr.1.eq_or_lt with h | h
  · subst h; simp; positivity
  rcases hr.2.eq_or_lt with h' | h'
  · subst h'; norm_num; positivity
  have := pw_two h h'
  norm_num at this ⊢
  exact this

lemma low {d : ℕ} (hd : 2 ≤ d) : (Real.log ((d : ℝ) - 1)) ^ 2 / 4 < maxVariance d := by
  have hk : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨r, hr, hlt⟩ := pw_low hk
  have hbdd : BddAbove (varianceObjective d '' Ioo 0 (1 / 2)) := by
    refine ⟨Real.log ((d : ℝ) - 1) ^ 2 / 4 + 1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (pw_easy hk hx.1 hx.2).le
  unfold maxVariance
  exact hlt.trans_le (le_csSup hbdd ⟨r, hr, rfl⟩)

lemma easy_le {d : ℕ} (hd : 3 ≤ d) : easyVariance d ≤ (Real.log d) ^ 2 := by
  unfold easyVariance
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hc0 : 0 ≤ Real.log ((d : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hcD : Real.log ((d : ℝ) - 1) ≤ Real.log d := Real.log_le_log (by linarith) (by linarith)
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  rcases hd.eq_or_lt with h | h
  · subst h
    have h12 : 19 * Real.log 2 < 12 * Real.log 3 := by
      have : Real.log ((2 : ℝ) ^ 19) < Real.log ((3 : ℝ) ^ 12) :=
        Real.log_lt_log (by norm_num) (by norm_num)
      simpa [Real.log_pow] using this
    norm_num at hcD hc0 ⊢
    nlinarith
  · have h4 : (4 : ℝ) ≤ d := by exact_mod_cast h
    have hD : 2 * Real.log 2 ≤ Real.log d := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num; linarith)
    nlinarith

theorem x8_main {d : ℕ} (hd : 2 ≤ d) :
    (Real.log ((d : ℝ) - 1)) ^ 2 / 4 < maxVariance d ∧
    maxVariance d < easyVariance d ∧ maxVariance d < (Real.log d) ^ 2 := by
  refine ⟨low hd, max_lt_easy hd, ?_⟩
  rcases hd.eq_or_lt with h | h
  · subst h; simpa using max_lt_two
  · exact (max_lt_easy hd).trans_le (easy_le h)

end X8L15

open QAlgorithms.Papers.Independent.Support50.P15 in
theorem solution {d : ℕ} (hd : 2 ≤ d) :
    (Real.log ((d : ℝ) - 1)) ^ 2 / 4 < maxVariance d ∧
    maxVariance d < easyVariance d ∧ maxVariance d < (Real.log d) ^ 2 :=
  X8L15.x8_main hd
