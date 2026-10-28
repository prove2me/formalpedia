-- Prove2me | solution 1 for TaoFivePrimes.positive_zero_nineteenth_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T19:10:55.036282+00:00
-- url     : https://prove2.me/submissions/3393faf5-e406-492b-9cae-4b3af4785e69

import Mathlib
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ZeroCountIncrement

/-!
# High inverse moments from a zero-count increment bound

The finite summation-by-parts proof is adapted from the published
`dusart_psi_433_20261014_ZeroAbel` definition. The nineteenth-moment calculation
below is new. Its count hypothesis is explicit and will be supplied by the
proved Riemann--von Mangoldt increment estimate for actual zeta zeros.
-/

set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory
namespace ShortPrimeIntervalTailMoments

def step (c x : ℝ) : ℝ := if c ≤ x then 1 else 0

theorem step_mono (c : ℝ) : Monotone (step c) := by
  intro x y hxy
  unfold step
  split_ifs <;> linarith

lemma integral_step_mul_deriv (a b c : ℝ) (hc : a ≤ c ∧ c ≤ b)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) :
    (∫ t in a..b, step c t * g' t) = g b - g c := by
  have hab : a ≤ b := hc.1.trans hc.2
  have hsub₁ : uIcc a c ⊆ Icc a b := by
    rw [uIcc_of_le hc.1]
    intro t ht
    exact ⟨ht.1, ht.2.trans hc.2⟩
  have hsub₂ : uIcc c b ⊆ Icc a b := by
    rw [uIcc_of_le hc.2]
    intro t ht
    exact ⟨hc.1.trans ht.1, ht.2⟩
  have hi₁ : IntervalIntegrable (fun t => step c t * g' t) volume a c :=
    ((step_mono c).intervalIntegrable (μ := volume)).mul_continuousOn (hcont.mono hsub₁)
  have hi₂ : IntervalIntegrable (fun t => step c t * g' t) volume c b :=
    ((step_mono c).intervalIntegrable (μ := volume)).mul_continuousOn (hcont.mono hsub₂)
  have hl : (∫ t in a..c, step c t * g' t) = 0 := by
    calc _ = ∫ _ in a..c, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hc.1
          intro t ht
          simp only [step, if_neg (not_le.mpr ht.2), zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have hu : (∫ t in c..b, step c t * g' t) = g b - g c := by
    calc _ = ∫ t in c..b, g' t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hc.2] at ht
          simp only [step, if_pos ht.1, one_mul]
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hderiv t (hsub₂ ht)) (hcont.mono hsub₂).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, hl, hu, zero_add]

def finiteCount {α : Type*} (Z : Finset α) (m : α → ℕ) (γ : α → ℝ) (t : ℝ) : ℝ :=
  ∑ ρ ∈ Z, (m ρ : ℝ) * step (γ ρ) t

lemma finite_zero_summation_by_parts {α : Type*} (Z : Finset α)
    (m : α → ℕ) (γ : α → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ γ ρ ∧ γ ρ ≤ b)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) :
    (∑ ρ ∈ Z, (m ρ : ℝ) * g (γ ρ)) =
      g b * (∑ ρ ∈ Z, (m ρ : ℝ)) -
        ∫ t in a..b, finiteCount Z m γ t * g' t := by
  have hi : ∀ ρ ∈ Z, IntervalIntegrable
      (fun t => (m ρ : ℝ) * step (γ ρ) t * g' t) volume a b := by
    intro ρ hρ
    exact (((step_mono (γ ρ)).intervalIntegrable (μ := volume)).const_mul _).mul_continuousOn
      (by simpa [uIcc_of_le hab] using hcont)
  have he : (fun t => finiteCount Z m γ t * g' t) =
      (fun t => ∑ ρ ∈ Z, (m ρ : ℝ) * step (γ ρ) t * g' t) := by
    funext t
    rw [finiteCount, Finset.sum_mul]
  rw [he, intervalIntegral.integral_finsetSum hi]
  have hval : ∀ ρ ∈ Z, (∫ t in a..b, (m ρ : ℝ) * step (γ ρ) t * g' t) =
      (m ρ : ℝ) * (g b - g (γ ρ)) := by
    intro ρ hρ
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul,
      integral_step_mul_deriv a b (γ ρ) (hγ ρ hρ) g g' hcont hderiv]
  rw [Finset.sum_congr rfl hval]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring


theorem finite_sum_le_primitive {ι : Type*} (Z : Finset ι) (w : ι → ℕ) (γ : ι → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hγ : ∀ z ∈ Z, a ≤ γ z ∧ γ z ≤ b)
    (g d W J : ℝ → ℝ) (hdcont : ContinuousOn d (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t)
    (hJ : ∀ t ∈ uIcc a b, HasDerivAt J (W t*d t) t)
    (hneg : ∀ t ∈ Icc a b, d t ≤ 0)
    (hcount : ∀ t ∈ Icc a b, finiteCount Z w γ t ≤ W t)
    (hg : 0 ≤ g b) (hend : g b*W b ≤ J b) :
    (∑ z ∈ Z, (w z : ℝ)*g (γ z)) ≤ J a := by
  have hiCount : IntervalIntegrable (finiteCount Z w γ) volume a b := by
    have h := IntervalIntegrable.sum (μ := volume) Z (fun z (_ : z ∈ Z) =>
      ((step_mono (γ z)).intervalIntegrable (μ := volume) (a := a) (b := b)).const_mul (w z : ℝ))
    convert h using 1 <;> try rfl
    funext t
    simp only [finiteCount, Finset.sum_apply]
  have hdcont' : ContinuousOn d (uIcc a b) := by simpa [uIcc_of_le hab] using hdcont
  have hW' : ContinuousOn W (uIcc a b) := by simpa [uIcc_of_le hab] using hW
  have hi := hiCount.mul_continuousOn hdcont'
  have hiW := (hW'.mul hdcont').intervalIntegrable (μ := volume)
  have hle := intervalIntegral.integral_mono_on hab hiW hi (fun t ht =>
    mul_le_mul_of_nonpos_right (hcount t ht) (hneg t ht))
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hJ hiW
  have hcnt : finiteCount Z w γ b = ∑ z ∈ Z, (w z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [step, if_pos (hγ z hz).2, mul_one]
  have hb := mul_le_mul_of_nonneg_left (hcount b ⟨hab, le_rfl⟩) hg
  rw [hcnt] at hb
  rw [finite_zero_summation_by_parts Z w γ a b hab hγ g d hdcont hd]
  simp only [Pi.mul_apply] at hle
  rw [hval] at hle
  linarith

noncomputable def countingMain (t : ℝ) : ℝ :=
  t/(2*Real.pi)*(Real.log (t/(2*Real.pi))-1)

private theorem log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  apply (Real.log_le_iff_le_exp (by positivity)).2
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.exp_one_gt_d9
    norm_num at hh ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 2
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith [Real.pi_lt_d2]

theorem finite_inverse_nineteenth_tail {ι : Type*} (Z : Finset ι) (w : ι → ℕ) (γ : ι → ℝ)
    (H : ℝ) (hH : 1000 ≤ H) (hγ : ∀ z ∈ Z, H < γ z)
    (hcountBound : ∀ t, H ≤ t → finiteCount Z w γ t ≤
      countingMain t - countingMain H + 9*Real.log (t+5) + 9*Real.log (H+5) + 158) :
    (∑ z ∈ Z, (w z : ℝ)*(1/(γ z)^19)) ≤
      (18*Real.log (H/(2*Real.pi))+1)/(648*Real.pi*H^18) +
        (18*Real.log H+3353/19)/H^19 := by
  classical
  have hH0 : 0 < H := by linarith
  let k : ℝ := 1 / (2 * Real.pi)
  let c : ℝ := Real.log (2 * Real.pi) + 1
  let D : ℝ := -k * H * (Real.log H - c) + 9 * Real.log H + 176
  let g : ℝ → ℝ := fun t => 1 / t^19
  let d : ℝ → ℝ := fun t => -19 / t^20
  let W : ℝ → ℝ := fun t => k * t * (Real.log t - c) + 9 * Real.log t + D
  let J : ℝ → ℝ := fun t =>
    k * ((19 / 18 : ℝ) * (Real.log t - c) + 19 / 324) / t^18 +
      (9 * Real.log t + (9 / 19 + D)) / t^19
  have hk : 0 < k := by dsimp [k]; positivity
  have hc : c ≤ 3 := by dsimp [c]; linarith [log_two_pi_le_two]
  have hF (t : ℝ) (ht : 0 < t) :
      countingMain t = k * t * (Real.log t - c) := by
    unfold countingMain
    rw [Real.log_div ht.ne' (by positivity)]
    dsimp [k, c]
    ring
  have hlog (t : ℝ) (ht : H ≤ t) : Real.log (t + 5) ≤ Real.log t + 1 := by
    have ht0 : 0 < t := hH0.trans_le ht
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh
      exact hh
    calc
      _ ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
      _ ≤ _ := by linarith
  have hJH : J H =
      (18*Real.log (H/(2*Real.pi))+1)/(648*Real.pi*H^18) +
      (18*Real.log H+3353/19)/H^19 := by
    dsimp [J, D, c, k]
    rw [Real.log_div hH0.ne' (by positivity)]
    field_simp [hH0.ne', Real.pi_ne_zero]
    ring
  by_cases hn : Z.Nonempty
  · let b : ℝ := max H (Z.sup' hn γ)
    have hab : H ≤ b := le_max_left _ _
    have hb0 : 0 < b := hH0.trans_le hab
    have hγb (ρ : ι) (hρ : ρ ∈ Z) : γ ρ ≤ b :=
      (Finset.le_sup' γ hρ).trans (le_max_right _ _)
    have hcont : ContinuousOn d (Icc H b) := by
      intro t ht
      have ht0 : 0 < t := hH0.trans_le ht.1
      apply ContinuousAt.continuousWithinAt
      dsimp [d]
      fun_prop (disch := positivity)
    have hW : ContinuousOn W (Icc H b) := by
      intro t ht
      have hn : t ≠ 0 := (hH0.trans_le ht.1).ne'
      apply ContinuousAt.continuousWithinAt
      dsimp [W]
      fun_prop (disch := assumption)
    have hd : ∀ t ∈ Icc H b, HasDerivAt g (d t) t := by
      intro t ht
      have hn : t ≠ 0 := (hH0.trans_le ht.1).ne'
      have hh := ((hasDerivAt_id t).pow 19).inv (pow_ne_zero 19 hn)
      have he : (id ^ 19 : ℝ → ℝ)⁻¹ = g := by funext u; simp [g]
      rw [he] at hh
      exact hh.congr_deriv (by dsimp [d]; field_simp [hn])
    have hJ : ∀ t ∈ uIcc H b, HasDerivAt J (W t * d t) t := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      have hn : t ≠ 0 := (hH0.trans_le ht.1).ne'
      have h1 := (((((Real.hasDerivAt_log hn).sub_const c).const_mul (19 / 18)).add_const
        (19 / 324)).const_mul k).div ((hasDerivAt_id t).pow 18) (pow_ne_zero 18 hn)
      have h2 := (((Real.hasDerivAt_log hn).const_mul 9).add_const (9 / 19 + D)).div
        ((hasDerivAt_id t).pow 19) (pow_ne_zero 19 hn)
      apply (h1.add h2).congr_deriv
      dsimp [W, d]
      field_simp [hn]
      ring
    have hcount : ∀ t ∈ Icc H b,
        finiteCount Z w γ t ≤ W t := by
      intro t ht
      have hi := hcountBound t ht.1
      rw [hF t (hH0.trans_le ht.1), hF H hH0] at hi
      have hlt := hlog t ht.1
      have hlH := hlog H le_rfl
      dsimp [W, D]
      linarith only [hi, hlt, hlH]
    have hend : g b * W b ≤ J b := by
      have hlogb : 3 ≤ Real.log b := by
        have he : Real.exp 3 ≤ (27 : ℝ) := by
          have hp := pow_le_pow_left₀ (Real.exp_pos 1).le
            (show Real.exp 1 ≤ (3 : ℝ) by linarith [Real.exp_one_lt_d9]) 3
          rw [← Real.exp_nat_mul] at hp
          norm_num at hp
          exact hp
        exact (Real.le_log_iff_exp_le hb0).mpr (he.trans (by linarith))
      have hdiff : 0 ≤ Real.log b - c := by linarith only [hlogb, hc]
      have hnonneg : 0 ≤ k * ((1 / 18 : ℝ) * (Real.log b - c) + 19 / 324) / b^18 + (9 / 19) / b^19 := by
        positivity
      have he : J b - g b * W b =
          k * ((1 / 18 : ℝ) * (Real.log b - c) + 19 / 324) / b^18 + (9 / 19) / b^19 := by
        dsimp [J, g, W]
        field_simp [hb0.ne']
        ring
      linarith only [he, hnonneg]
    have hh := finite_sum_le_primitive Z w γ H b hab
      (fun ρ hρ => ⟨(hγ ρ hρ).le, hγb ρ hρ⟩) g d W J hcont hW hd hJ
      (fun t _ => by dsimp [d]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
      hcount (by dsimp [g]; positivity) hend
    exact hh.trans_eq hJH
  · have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty]
    have hl : 0 ≤ Real.log (H / (2 * Real.pi)) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ (by positivity)).2
      linarith [Real.pi_lt_four]
    have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    positivity

theorem nineteenth_majorant_le_quarter (H : ℝ) (hH : (10 : ℝ)^8 ≤ H)
    (hlog : Real.log H ≤ 22) :
    (18*Real.log (H/(2*Real.pi))+1)/(648*Real.pi*H^18) +
      (18*Real.log H+3353/19)/H^19 ≤ 1/(4*H^18) := by
  have hH0 : 0 < H := by norm_num at hH; linarith
  have hlogratio : Real.log (H/(2*Real.pi)) ≤ 22 := by
    apply le_trans (Real.log_le_log (by positivity)
      (div_le_self hH0.le (by linarith [Real.pi_gt_three]))) hlog
  have h1 : (18*Real.log (H/(2*Real.pi))+1)/(648*Real.pi*H^18) ≤
      (397/1944 : ℝ)/H^18 := by
    calc
      _ ≤ 397/(648*Real.pi*H^18) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 397/(1944*H^18) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (pow_nonneg hH0.le 18)])
      _ = _ := by ring
  have h2 : (18*Real.log H+3353/19)/H^19 ≤ (573/(10 : ℝ)^8)/H^18 := by
    calc
      _ ≤ 573/H^19 := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = (573/H)/H^18 := by rw [pow_succ]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH) (by positivity)
  calc
    _ ≤ (397/1944 : ℝ)/H^18 + (573/(10 : ℝ)^8)/H^18 := add_le_add h1 h2
    _ = ((397/1944 : ℝ)+573/(10 : ℝ)^8)/H^18 := by ring
    _ ≤ (1/4 : ℝ)/H^18 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

theorem finite_inverse_nineteenth_tail_le_quarter {ι : Type*}
    (Z : Finset ι) (w : ι → ℕ) (γ : ι → ℝ) (H : ℝ)
    (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22) (hγ : ∀ z ∈ Z, H < γ z)
    (hcountBound : ∀ t, H ≤ t → finiteCount Z w γ t ≤
      countingMain t-countingMain H+9*Real.log (t+5)+9*Real.log (H+5)+158) :
    (∑ z ∈ Z, (w z : ℝ)*(1/(γ z)^19)) ≤ 1/(4*H^18) :=
  (finite_inverse_nineteenth_tail Z w γ H (by norm_num at hH ⊢; linarith) hγ hcountBound).trans
    (nineteenth_majorant_le_quarter H hH hlog)

end ShortPrimeIntervalTailMoments

theorem solution (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22)
    (hγ : ∀ ρ ∈ Z, H < ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/ρ.im^19)) ≤ 1/(4*H^18) := by
  apply ShortPrimeIntervalTailMoments.finite_inverse_nineteenth_tail_le_quarter
    Z DusartSmoothing.RvM.zeroMult Complex.im H hH hlog hγ
  intro t ht
  have h := ExplicitPNT.DusartTable1.Modules.ZeroCountIncrement.2 Z hZ H t
    (by norm_num at hH ⊢; linarith) ht hγ
  convert h using 1 <;> rfl
