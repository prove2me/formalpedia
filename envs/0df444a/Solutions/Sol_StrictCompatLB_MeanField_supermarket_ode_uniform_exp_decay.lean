-- Prove2me | solution 1 for StrictCompatLB.MeanField.supermarket_ode_uniform_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:55:07.073853+00:00
-- url     : https://prove2.me/submissions/ce9115d3-f1ef-4834-ab0c-fdc5e9bfdb2d

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace SC77K8

open StrictCompatLB.MeanField

/-! K8 work file, part 1: weights and the column-sum (generator) inequality
`lam a_i (w_{i+1} - w_i) - w_i + w_{i-1} ≤ -δ w_i`, plus the bound on
`a_i = (x_i^d - π_i^d)/(x_i - π_i)` above `i0Index`. -/

/-- weight `w i = (1 - q^i)/(1-q)` up to `i0`, then geometric with ratio `1 + η`. -/
noncomputable def wt (lam q : ℝ) (i0 : ℕ) (i : ℕ) : ℝ :=
  if i ≤ i0 then (1 - q ^ i) / (1 - q)
  else (1 - q ^ i0) / (1 - q) * (1 + q ^ i0 * (1 - lam) / 8) ^ (i - i0)

section weights

variable {lam q : ℝ} {i0 : ℕ}

lemma wt_le (i : ℕ) (hi : i ≤ i0) : wt lam q i0 i = (1 - q ^ i) / (1 - q) := by
  simp [wt, hi]

lemma wt_tail (hq1 : q < 1) (i : ℕ) (hi : i0 ≤ i) :
    wt lam q i0 i = (1 - q ^ i0) / (1 - q) * (1 + q ^ i0 * (1 - lam) / 8) ^ (i - i0) := by
  rcases eq_or_lt_of_le hi with h | h
  · subst h; simp [wt]
  · have : ¬ i ≤ i0 := by omega
    simp [wt, this]

lemma wt_step (hq1 : q < 1) (i : ℕ) :
    (1 - q ^ (i + 1)) / (1 - q) - (1 - q ^ i) / (1 - q) = q ^ i := by
  have h : (1 - q) ≠ 0 := by linarith
  field_simp
  ring

lemma W_bounds (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (i : ℕ) :
    0 ≤ (1 - q ^ i) / (1 - q) ∧ (1 - q ^ i) / (1 - q) ≤ 2 := by
  have h1 : 0 < 1 - q := by linarith
  have hp0 : 0 ≤ q ^ i := pow_nonneg hq0 i
  have hp1 : q ^ i ≤ 1 := pow_le_one₀ hq0 (by linarith)
  constructor
  · exact div_nonneg (by linarith) h1.le
  · rw [div_le_iff₀ h1]; linarith

/-- The column-sum inequality, all three regimes. -/
theorem coef_le (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ)
    (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hqd : lam * d * q ≤ 1 / 2) (hi0 : 1 ≤ i0)
    (i : ℕ) (hi : 1 ≤ i) (a : ℝ) (ha0 : 0 ≤ a) (had : a ≤ d)
    (hatail : i0 ≤ i → lam * a ≤ (1 + lam) / 2) :
    lam * a * (wt lam q i0 (i + 1) - wt lam q i0 i) - wt lam q i0 i + wt lam q i0 (i - 1)
      ≤ -(q ^ i0 * (1 - lam) / 8 * (1 - lam) / 4) * wt lam q i0 i := by
  have hq1 : q < 1 := by linarith
  have h1q : 0 < 1 - q := by linarith
  set η := q ^ i0 * (1 - lam) / 8 with hη
  set W := (1 - q ^ i0) / (1 - q) with hW
  have hqi0 : 0 < q ^ i0 := pow_pos hq0 i0
  have hqi0' : q ^ i0 ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hlm : 0 < 1 - lam := by linarith
  have hη0 : 0 < η := by
    rw [hη]; positivity
  have hη1 : η ≤ (1 - lam) / 8 := by
    rw [hη]; nlinarith
  have hηq : η ≤ q ^ i0 / 8 := by
    rw [hη]; nlinarith
  have hδ0 : 0 ≤ η * (1 - lam) / 4 := by positivity
  have hδη : η * (1 - lam) / 4 ≤ η / 4 := by nlinarith
  obtain ⟨hW0, hW2⟩ := W_bounds hq0.le hq i0
  have hla : lam * a ≤ lam * d := mul_le_mul_of_nonneg_left had hlam0.le
  have hla0 : 0 ≤ lam * a := mul_nonneg hlam0.le ha0
  rcases lt_trichotomy i i0 with hlt | heq | hgt
  · -- below i0
    have e1 : wt lam q i0 (i + 1) = (1 - q ^ (i + 1)) / (1 - q) := wt_le _ (by omega)
    have e2 : wt lam q i0 i = (1 - q ^ i) / (1 - q) := wt_le _ (by omega)
    have e3 : wt lam q i0 (i - 1) = (1 - q ^ (i - 1)) / (1 - q) := wt_le _ (by omega)
    obtain ⟨hwi0, hwi2⟩ := W_bounds hq0.le hq i
    have hs1 := wt_step hq1 i
    have hs2 := wt_step hq1 (i - 1)
    have hii : i - 1 + 1 = i := by omega
    rw [hii] at hs2
    have hqi : q ^ i = q * q ^ (i - 1) := by rw [← pow_succ', hii]
    have hp0 : 0 ≤ q ^ (i - 1) := pow_nonneg hq0.le _
    have hpi0 : q ^ i0 ≤ q ^ (i - 1) := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    rw [e1, e2, e3, hs1]
    have key1 : lam * a * q ^ i ≤ q ^ (i - 1) / 2 := by
      have h1 : lam * a * q ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_right hla hq0.le
        linarith
      rw [hqi, ← mul_assoc]
      have := mul_le_mul_of_nonneg_right h1 hp0
      linarith
    have h3 : (η * (1 - lam) / 4) * ((1 - q ^ i) / (1 - q)) ≤ η / 4 * 2 :=
      mul_le_mul hδη hwi2 hwi0 (by positivity)
    linarith
  · -- at i0
    subst i
    have e1 : wt lam q i0 (i0 + 1) = W * (1 + η) := by
      rw [wt_tail hq1 _ (by omega), show i0 + 1 - i0 = 1 by omega, pow_one]
    have e2 : wt lam q i0 i0 = W := wt_le _ le_rfl
    have e3 : wt lam q i0 (i0 - 1) = (1 - q ^ (i0 - 1)) / (1 - q) := wt_le _ (by omega)
    have hs2 := wt_step hq1 (i0 - 1)
    have hii : i0 - 1 + 1 = i0 := by omega
    rw [hii] at hs2
    have hqi : q ^ i0 = q * q ^ (i0 - 1) := by rw [← pow_succ', hii]
    have hp0 : 0 ≤ q ^ (i0 - 1) := pow_nonneg hq0.le _
    rw [e1, e2, e3]
    have hla1 : lam * a ≤ 1 := by have := hatail le_rfl; linarith
    have hηp : η ≤ q ^ (i0 - 1) / 16 := by
      have := mul_le_mul_of_nonneg_right hq hp0
      rw [hqi] at hηq; linarith
    have hWp : W - (1 - q ^ (i0 - 1)) / (1 - q) = q ^ (i0 - 1) := hs2
    have t1 : lam * a * (W * (1 + η) - W) = lam * a * W * η := by ring
    have t2 : lam * a * W * η ≤ 1 * 2 * η :=
      mul_le_mul_of_nonneg_right (mul_le_mul hla1 hW2 hW0 zero_le_one) hη0.le
    have t3 : (η * (1 - lam) / 4) * W ≤ η / 4 * 2 :=
      mul_le_mul hδη hW2 hW0 (by positivity)
    nlinarith [t1, t2, t3, hηp, hWp]
  · -- above i0
    have hii : i - 1 - i0 + 1 = i - i0 := by omega
    set v := W * (1 + η) ^ (i - 1 - i0) with hv
    have e1 : wt lam q i0 (i + 1) = v * (1 + η) ^ 2 := by
      rw [wt_tail hq1 _ (by omega), hv, mul_assoc, ← pow_add]; congr 2; omega
    have e2 : wt lam q i0 i = v * (1 + η) := by
      rw [wt_tail hq1 _ (by omega), hv, mul_assoc, ← pow_succ, hii]
    have e3 : wt lam q i0 (i - 1) = v := by
      rw [wt_tail hq1 _ (by omega)]
    have hv0 : 0 ≤ v := by rw [hv]; exact mul_nonneg hW0 (pow_nonneg (by linarith) _)
    rw [e1, e2, e3]
    have hA := hatail hgt.le
    have hA1 : lam * a ≤ 1 := by linarith
    have hAη : lam * a * η ≤ 1 * η := mul_le_mul_of_nonneg_right hA1 hη0.le
    have hlη : (1 - lam) * η ≤ 1 * η := mul_le_mul_of_nonneg_right (by linarith) hη0.le
    have inner : lam * a * (1 + η) - 1 + (1 - lam) / 4 * (1 + η) ≤ 0 := by
      have x1 : lam * a * (1 + η) = lam * a + lam * a * η := by ring
      have x2 : (1 - lam) / 4 * (1 + η) = (1 - lam) / 4 + (1 - lam) * η / 4 := by ring
      rw [x1, x2]; linarith
    have br := mul_nonpos_of_nonneg_of_nonpos hv0 (mul_nonpos_of_nonneg_of_nonpos hη0.le inner)
    have hid : lam * a * (v * (1 + η) ^ 2 - v * (1 + η)) - v * (1 + η) + v
        + η * (1 - lam) / 4 * (v * (1 + η))
        = v * (η * (lam * a * (1 + η) - 1 + (1 - lam) / 4 * (1 + η))) := by ring
    linarith

end weights

/-! Part 2: `a_i` bound. -/

lemma geom_bound (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (d : ℕ) :
    ∑ j ∈ Finset.range d, p ^ j ≤ 1 + 2 * p := by
  have h := geom_sum_mul_neg p d
  have hpd : 0 ≤ p ^ d := pow_nonneg hp0 d
  have hs0 : 0 ≤ ∑ j ∈ Finset.range d, p ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hp0 j)
  nlinarith

lemma a_facts (x p : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (d : ℕ) :
    let a := ∑ k ∈ Finset.range d, x ^ k * p ^ (d - 1 - k)
    x ^ d - p ^ d = a * (x - p) ∧ 0 ≤ a ∧ a ≤ d ∧ a ≤ ∑ j ∈ Finset.range d, p ^ j := by
  intro a
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (geom_sum₂_mul x p d).symm
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hx0 _) (pow_nonneg hp0 _))
  · have : a ≤ ∑ _k ∈ Finset.range d, (1 : ℝ) :=
      Finset.sum_le_sum (fun k _ => by
        have := pow_le_one₀ hx0 hx1 (n := k)
        have := pow_le_one₀ hp0 hp1 (n := d - 1 - k)
        have := pow_nonneg hp0 (d - 1 - k)
        nlinarith)
    simpa using this
  · have h1 : a ≤ ∑ k ∈ Finset.range d, p ^ (d - 1 - k) :=
      Finset.sum_le_sum (fun k _ => by
        have := pow_le_one₀ hx0 hx1 (n := k)
        have := pow_nonneg hp0 (d - 1 - k)
        nlinarith)
    rwa [Finset.sum_range_reflect (fun j => p ^ j) d] at h1

/-! Part 3: `i0Index` facts. -/

lemma fp_le_pow (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (d : ℕ) (hd : 1 ≤ d) (i : ℕ) :
    PowerTwoChoices.Limit.fixedPoint lam d i ≤ lam ^ i := by
  unfold PowerTwoChoices.Limit.fixedPoint
  apply pow_le_pow_of_le_one hlam0 hlam1
  calc i = ∑ _k ∈ Finset.range i, 1 := by simp
    _ ≤ ∑ k ∈ Finset.range i, d ^ k :=
        Finset.sum_le_sum (fun k _ => Nat.one_le_pow _ _ (by omega))

lemma fp_anti (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (d : ℕ) {i j : ℕ} (hij : i ≤ j) :
    PowerTwoChoices.Limit.fixedPoint lam d j ≤ PowerTwoChoices.Limit.fixedPoint lam d i := by
  unfold PowerTwoChoices.Limit.fixedPoint
  exact pow_le_pow_of_le_one hlam0 hlam1
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) (fun _ _ _ => Nat.zero_le _))

lemma fp_nonneg (lam : ℝ) (hlam0 : 0 ≤ lam) (d i : ℕ) :
    0 ≤ PowerTwoChoices.Limit.fixedPoint lam d i := by
  unfold PowerTwoChoices.Limit.fixedPoint; exact pow_nonneg hlam0 _

theorem i0_facts (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 2 ≤ d) :
    1 ≤ i0Index lam d ∧
    (∀ i, i0Index lam d ≤ i →
      lam * (2 * PowerTwoChoices.Limit.fixedPoint lam d i + 1) < (1 + lam) / 2) ∧
    (∀ i, i0Index lam d ≤ i → PowerTwoChoices.Limit.fixedPoint lam d i ≤ 1 / 2) := by
  set S := {i : ℕ | 1 ≤ i ∧
    lam * (2 * PowerTwoChoices.Limit.fixedPoint lam d i + 1) < (1 + lam) / 2} with hS
  have hne : S.Nonempty := by
    have ht : Tendsto (fun n : ℕ => lam ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1
    have hpos : 0 < (1 - lam) / (4 * lam) := by
      apply div_pos <;> linarith
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    refine ⟨N + 1, by omega, ?_⟩
    have h1 := hN (N + 1) (by omega)
    have h2 := fp_le_pow lam hlam0.le hlam1.le d (by omega) (N + 1)
    rw [lt_div_iff₀ (by linarith)] at h1
    nlinarith
  have hmem : i0Index lam d ∈ S := Nat.sInf_mem hne
  have hmem' := hmem
  obtain ⟨h1, h2⟩ := hmem'
  have hall : ∀ i, i0Index lam d ≤ i →
      lam * (2 * PowerTwoChoices.Limit.fixedPoint lam d i + 1) < (1 + lam) / 2 := by
    intro i hi
    have := fp_anti lam hlam0.le hlam1.le d hi
    nlinarith
  refine ⟨h1, hall, ?_⟩
  intro i hi
  have hfi := hall i hi
  have hfl : PowerTwoChoices.Limit.fixedPoint lam d i ≤ lam := by
    have := fp_le_pow lam hlam0.le hlam1.le d (by omega) i
    have : lam ^ i ≤ lam ^ 1 := pow_le_pow_of_le_one hlam0.le hlam1.le (by omega)
    simp at this; linarith
  have hf0 := fp_nonneg lam hlam0.le d i
  by_contra hc
  have hc' : 1 / 2 < PowerTwoChoices.Limit.fixedPoint lam d i := lt_of_not_ge hc
  nlinarith

/-! Part 4: right derivative of `|f|`. -/

theorem abs_rderiv {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivWithinAt f f' (Set.Ici t) t) :
    ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ sg * f t = |f t| ∧
      HasDerivWithinAt (fun u => |f u|) (sg * f') (Set.Ici t) t := by
  rcases lt_trichotomy (f t) 0 with hneg | hzero | hpos
  · refine ⟨-1, Or.inr rfl, by rw [abs_of_neg hneg]; ring, ?_⟩
    have hev : ∀ᶠ u in 𝓝[Set.Ici t] t, f u < 0 :=
      hf.continuousWithinAt.eventually (gt_mem_nhds hneg)
    have h2 : (fun u => |f u|) =ᶠ[𝓝[Set.Ici t] t] fun u => -f u :=
      hev.mono (fun u hu => abs_of_neg hu)
    have := hf.neg.congr_of_eventuallyEq h2 (abs_of_neg hneg)
    simpa using this
  · refine ⟨if 0 ≤ f' then 1 else -1, by split_ifs <;> simp, by rw [hzero]; simp, ?_⟩
    rw [hasDerivWithinAt_iff_isLittleO] at hf ⊢
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hf
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0 ≤ u - t := sub_nonneg.mpr hu
    simp only [hzero, abs_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
    have key : (u - t) * ((if 0 ≤ f' then 1 else -1) * f') = |(u - t) * f'| := by
      rw [abs_mul, abs_of_nonneg hu']
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    rw [key]
    exact abs_abs_sub_abs_le_abs_sub _ _
  · refine ⟨1, Or.inl rfl, by rw [abs_of_pos hpos]; ring, ?_⟩
    have hev : ∀ᶠ u in 𝓝[Set.Ici t] t, 0 < f u :=
      hf.continuousWithinAt.eventually (lt_mem_nhds hpos)
    have h2 : (fun u => |f u|) =ᶠ[𝓝[Set.Ici t] t] f :=
      hev.mono (fun u hu => abs_of_pos hu)
    have := hf.congr_of_eventuallyEq h2 (abs_of_pos hpos)
    simpa using this

end SC77K8

set_option autoImplicit false

open Filter Topology Set
open scoped ENNReal

namespace SC77K8B

open PowerTwoChoices.Limit

/-! K8 part 2 (analysis), generic in the weights `w`. -/

/-- Gronwall with right derivatives on `[0, t]`. -/
theorem gron {f : ℝ → ℝ} {t K ε δ0 : ℝ} (hc : ContinuousOn f (Icc 0 t))
    (hd : ∀ v ∈ Ico 0 t, ∃ D, HasDerivWithinAt f D (Ici v) v ∧ D ≤ K * f v + ε)
    (h0 : f 0 ≤ δ0) : ∀ v ∈ Icc 0 t, f v ≤ gronwallBound δ0 K ε v := by
  intro v hv
  have := le_gronwallBound_of_liminf_deriv_right_le (f' := fun v => K * f v + ε) hc
    (fun x hx r hr => by
      obtain ⟨D, hD, hDle⟩ := hd x hx
      have := hD.liminf_right_slope_le (lt_of_le_of_lt hDle hr)
      simpa [slope, smul_eq_mul] using this) h0 (fun x _ => le_rfl) v hv
  simpa using this

theorem abs_rderiv {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivWithinAt f f' (Set.Ici t) t) :
    ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ sg * f t = |f t| ∧
      HasDerivWithinAt (fun u => |f u|) (sg * f') (Set.Ici t) t := by
  rcases lt_trichotomy (f t) 0 with hneg | hzero | hpos
  · refine ⟨-1, Or.inr rfl, by rw [abs_of_neg hneg]; ring, ?_⟩
    have hev : ∀ᶠ u in 𝓝[Set.Ici t] t, f u < 0 :=
      hf.continuousWithinAt.eventually (gt_mem_nhds hneg)
    have h2 : (fun u => |f u|) =ᶠ[𝓝[Set.Ici t] t] fun u => -f u :=
      hev.mono (fun u hu => abs_of_neg hu)
    have := hf.neg.congr_of_eventuallyEq h2 (abs_of_neg hneg)
    simpa using this
  · refine ⟨if 0 ≤ f' then 1 else -1, by split_ifs <;> simp, by rw [hzero]; simp, ?_⟩
    rw [hasDerivWithinAt_iff_isLittleO] at hf ⊢
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hf
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0 ≤ u - t := sub_nonneg.mpr hu
    simp only [hzero, abs_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
    have key : (u - t) * ((if 0 ≤ f' then 1 else -1) * f') = |(u - t) * f'| := by
      rw [abs_mul, abs_of_nonneg hu']
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    rw [key]
    exact abs_abs_sub_abs_le_abs_sub _ _
  · refine ⟨1, Or.inl rfl, by rw [abs_of_pos hpos]; ring, ?_⟩
    have hev : ∀ᶠ u in 𝓝[Set.Ici t] t, 0 < f u :=
      hf.continuousWithinAt.eventually (lt_mem_nhds hpos)
    have h2 : (fun u => |f u|) =ᶠ[𝓝[Set.Ici t] t] f :=
      hev.mono (fun u hu => abs_of_pos hu)
    have := hf.congr_of_eventuallyEq h2 (abs_of_pos hpos)
    simpa using this

lemma st_le_one {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) : x i ≤ 1 := by
  have := hx.2.2 (Nat.zero_le i); rw [hx.1] at this; exact this

lemma drift_le {lam : ℝ} (hlam : 0 ≤ lam) {d : ℕ} {x : ℕ → ℝ} (hx : IsState x) (j : ℕ) :
    drift lam d x j ≤ lam * x (j - 1) ^ d := by
  unfold drift
  have h1 : x (j + 1) ≤ x j := hx.2.2 (Nat.le_succ j)
  have h2 : 0 ≤ x j ^ d := pow_nonneg (hx.2.1 j) d
  nlinarith [mul_nonneg hlam h2]

lemma fp_succ (lam : ℝ) (d i : ℕ) :
    fixedPoint lam d (i + 1) = lam * fixedPoint lam d i ^ d := by
  unfold fixedPoint
  have hS : ∑ k ∈ Finset.range (i + 1), d ^ k = (∑ k ∈ Finset.range i, d ^ k) * d + 1 := by
    rw [Finset.sum_range_succ', Finset.sum_mul]; simp [pow_succ]
  rw [hS, pow_succ, pow_mul]; ring

lemma drift_fp (lam : ℝ) (d i : ℕ) (hi : 1 ≤ i) : drift lam d (fixedPoint lam d) i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  unfold drift
  simp only [Nat.add_sub_cancel]
  rw [fp_succ lam d (j + 1), fp_succ lam d j]; ring

section traj

variable {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}

lemma tr_deriv (hs : IsTrajectory lam d s) {i : ℕ} (hi : 1 ≤ i) {v : ℝ} (hv : 0 ≤ v) :
    HasDerivWithinAt (fun u => s u i) (drift lam d (s v) i) (Ici v) v :=
  (hs.2 i hi v hv).mono (Ici_subset_Ici.mpr hv)

lemma tr_cont (hs : IsTrajectory lam d s) {i : ℕ} (hi : 1 ≤ i) (t : ℝ) :
    ContinuousOn (fun u => s u i) (Icc 0 t) :=
  fun v hv => ((hs.2 i hi v hv.1).continuousWithinAt).mono (fun u hu => hu.1)

/-- tail block `∑_{k<m} w_{n+1+k} x_{n+1+k}`. -/
noncomputable def T (w : ℕ → ℝ) (s : ℝ → ℕ → ℝ) (n m : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, w (k + (n + 1)) * s v (k + (n + 1))

theorem T_gron (hlam0 : 0 < lam) (hlam1 : lam < 1) (hs : IsTrajectory lam d s) (hd : 1 ≤ d)
    {w : ℕ → ℝ} (hwnn : ∀ i, 0 ≤ w i) (hw2 : ∀ i, 1 ≤ i → w (i + 1) ≤ 2 * w i)
    (n m : ℕ) (t β : ℝ) (hβ : ∀ v ∈ Ico 0 t, lam * w (n + 1) * s v n ^ d ≤ β) :
    ∀ v ∈ Icc 0 t, T w s n m v ≤ gronwallBound (T w s n m 0) 2 β v := by
  apply gron
  · unfold T
    exact continuousOn_finsetSum _ (fun k _ =>
      continuousOn_const.mul (tr_cont hs (i := k + (n + 1)) (by omega) t))
  · intro v hv
    have hx := hs.1 v hv.1
    refine ⟨∑ k ∈ Finset.range m, w (k + (n + 1)) * drift lam d (s v) (k + (n + 1)), ?_, ?_⟩
    · unfold T
      have h := HasDerivWithinAt.sum (u := Finset.range m)
        (A := fun k y => w (k + (n + 1)) * s y (k + (n + 1)))
        (fun k _ => (tr_deriv hs (i := k + (n + 1)) (by omega) hv.1).const_mul _)
      rw [Finset.sum_fn] at h
      exact h
    · have hb := hβ v hv
      have hβ0 : 0 ≤ β := le_trans (mul_nonneg (mul_nonneg hlam0.le (hwnn _))
        (pow_nonneg (hx.2.1 n) d)) hb
      calc ∑ k ∈ Finset.range m, w (k + (n + 1)) * drift lam d (s v) (k + (n + 1))
          ≤ ∑ k ∈ Finset.range m, w (k + (n + 1)) * (lam * s v (k + n) ^ d) := by
            apply Finset.sum_le_sum
            intro k _
            have := drift_le (d := d) hlam0.le hx (k + (n + 1))
            rw [show k + (n + 1) - 1 = k + n by omega] at this
            exact mul_le_mul_of_nonneg_left this (hwnn _)
        _ ≤ 2 * T w s n m v + β := by
            rcases m with _ | m
            · simp [T]; exact hβ0
            · rw [Finset.sum_range_succ']
              have h1 : ∑ k ∈ Finset.range m, w (k + 1 + (n + 1)) * (lam * s v (k + 1 + n) ^ d)
                  ≤ ∑ k ∈ Finset.range m, 2 * (w (k + (n + 1)) * s v (k + (n + 1))) := by
                apply Finset.sum_le_sum
                intro k _
                rw [show k + 1 + n = k + (n + 1) by omega,
                  show k + 1 + (n + 1) = (k + (n + 1)) + 1 by omega]
                have hw := hw2 (k + (n + 1)) (by omega)
                have hx0 := hx.2.1 (k + (n + 1))
                have hx1 := st_le_one hx (k + (n + 1))
                have hpow : s v (k + (n + 1)) ^ d ≤ s v (k + (n + 1)) :=
                  pow_le_of_le_one hx0 hx1 (by omega)
                have hp0 : 0 ≤ s v (k + (n + 1)) ^ d := pow_nonneg hx0 d
                have hl : lam * s v (k + (n + 1)) ^ d ≤ s v (k + (n + 1)) := by nlinarith
                have hl0 : 0 ≤ lam * s v (k + (n + 1)) ^ d := mul_nonneg hlam0.le hp0
                calc w (k + (n + 1) + 1) * (lam * s v (k + (n + 1)) ^ d)
                    ≤ (2 * w (k + (n + 1))) * (lam * s v (k + (n + 1)) ^ d) :=
                      mul_le_mul_of_nonneg_right hw hl0
                  _ ≤ (2 * w (k + (n + 1))) * s v (k + (n + 1)) :=
                      mul_le_mul_of_nonneg_left hl (by linarith [hwnn (k + (n + 1))])
                  _ = 2 * (w (k + (n + 1)) * s v (k + (n + 1))) := by ring
              have h2 : ∑ k ∈ Finset.range m, 2 * (w (k + (n + 1)) * s v (k + (n + 1)))
                  ≤ 2 * T w s n (m + 1) v := by
                unfold T
                rw [← Finset.mul_sum, Finset.sum_range_succ]
                have := mul_nonneg (hwnn (m + (n + 1))) (hx.2.1 (m + (n + 1)))
                linarith
              simp only [zero_add]
              linarith
  · exact le_rfl

/-- truncated weighted potential `∑_{i=1}^n w_i |x_i - π_i|`. -/
noncomputable def P (lam : ℝ) (d : ℕ) (w : ℕ → ℝ) (s : ℝ → ℕ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, w (k + 1) * |s v (k + 1) - fixedPoint lam d (k + 1)|

end traj

lemma tele (w b u : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, w (k + 1) * (b k - b (k + 1) - u (k + 1) + u (k + 1 + 1)) =
    ∑ k ∈ Finset.range n,
        (b (k + 1) * (w (k + 1 + 1) - w (k + 1)) - w (k + 1) * u (k + 1) + w k * u (k + 1))
      - w (n + 1) * b n + w n * u (n + 1) + w 1 * b 0 - w 0 * u 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

lemma alg (n : ℕ) (lam δ : ℝ) (w a e sg D : ℕ → ℝ) (hlam : 0 ≤ lam) (hw0 : w 0 = 0)
    (hwnn : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (he0 : e 0 = 0)
    (hsg : ∀ k, sg k = 1 ∨ sg k = -1) (hsge : ∀ k, sg k * e (k + 1) = |e (k + 1)|)
    (hD : ∀ k, D k = lam * (a k * e k - a (k + 1) * e (k + 1)) - (e (k + 1) - e (k + 1 + 1)))
    (hcoef : ∀ i, 1 ≤ i → lam * a i * (w (i + 1) - w i) - w i + w (i - 1) ≤ -δ * w i) :
    ∑ k ∈ Finset.range n, w (k + 1) * (sg k * D k)
      ≤ -δ * ∑ k ∈ Finset.range n, w (k + 1) * |e (k + 1)| + w n * |e (n + 1)| := by
  have sgle : ∀ k y, sg k * y ≤ |y| := by
    intro k y
    rcases hsg k with h | h <;> rw [h]
    · simpa using le_abs_self y
    · simpa using neg_le_abs y
  have hterm : ∀ k ∈ Finset.range n, w (k + 1) * (sg k * D k) ≤ w (k + 1) *
      (lam * a k * |e k| - lam * a (k + 1) * |e (k + 1)| - |e (k + 1)| + |e (k + 1 + 1)|) := by
    intro k _
    apply mul_le_mul_of_nonneg_left _ (hwnn _)
    have expand : sg k * D k = lam * a k * (sg k * e k) - lam * a (k + 1) * (sg k * e (k + 1))
        - sg k * e (k + 1) + sg k * e (k + 1 + 1) := by rw [hD k]; ring
    rw [expand, hsge k]
    have h1 := mul_le_mul_of_nonneg_left (sgle k (e k)) (mul_nonneg hlam (ha k))
    have h2 := sgle k (e (k + 1 + 1))
    linarith
  have hT := tele w (fun i => lam * a i * |e i|) (fun i => |e i|) n
  have hs2 : ∑ k ∈ Finset.range n, (lam * a (k + 1) * |e (k + 1)| * (w (k + 1 + 1) - w (k + 1))
      - w (k + 1) * |e (k + 1)| + w k * |e (k + 1)|)
      ≤ ∑ k ∈ Finset.range n, -δ * (w (k + 1) * |e (k + 1)|) := by
    apply Finset.sum_le_sum
    intro k _
    have := hcoef (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    nlinarith [abs_nonneg (e (k + 1))]
  rw [← Finset.mul_sum] at hs2
  have hb : 0 ≤ w (n + 1) * (lam * a n * |e n|) :=
    mul_nonneg (hwnn _) (mul_nonneg (mul_nonneg hlam (ha n)) (abs_nonneg _))
  have h0 : w 1 * (lam * a 0 * |e 0|) - w 0 * |e 1| = 0 := by rw [he0, hw0]; simp
  have := Finset.sum_le_sum hterm
  linarith

section traj2

variable {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}

theorem P_gron (hlam0 : 0 < lam) (hlam1 : lam < 1) (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} (hw0 : w 0 = 0) (hwnn : ∀ i, 0 ≤ w i)
    (A : ℝ → ℝ → ℝ) (hA : ∀ x p : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ p → p ≤ 1 →
      x ^ d - p ^ d = A x p * (x - p) ∧ 0 ≤ A x p)
    {δ : ℝ} (hcoef : ∀ x : ℕ → ℝ, IsState x → ∀ i, 1 ≤ i →
      lam * A (x i) (fixedPoint lam d i) * (w (i + 1) - w i) - w i + w (i - 1) ≤ -δ * w i)
    (n : ℕ) (t ε : ℝ)
    (hε : ∀ v ∈ Ico 0 t, w n * |s v (n + 1) - fixedPoint lam d (n + 1)| ≤ ε) :
    ∀ v ∈ Icc 0 t, P lam d w s n v ≤ gronwallBound (P lam d w s n 0) (-δ) ε v := by
  have hp0 : ∀ i, 0 ≤ fixedPoint lam d i := fun i => pow_nonneg hlam0.le _
  have hp1 : ∀ i, fixedPoint lam d i ≤ 1 := fun i => pow_le_one₀ hlam0.le hlam1.le
  apply gron
  · unfold P
    exact continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul
      (((tr_cont hs (i := k + 1) (by omega) t).sub continuousOn_const).abs))
  · intro v hv
    have hx := hs.1 v hv.1
    have hsg : ∀ k, ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
        sg * (s v (k + 1) - fixedPoint lam d (k + 1)) = |s v (k + 1) - fixedPoint lam d (k + 1)| ∧
        HasDerivWithinAt (fun u => |s u (k + 1) - fixedPoint lam d (k + 1)|)
          (sg * drift lam d (s v) (k + 1)) (Ici v) v := by
      intro k
      obtain ⟨sg, h1, h2, h3⟩ :=
        abs_rderiv ((tr_deriv hs (i := k + 1) (by omega) hv.1).sub_const (fixedPoint lam d (k + 1)))
      exact ⟨sg, h1, h2, h3⟩
    choose sg hsg1 hsg2 hsg3 using hsg
    refine ⟨∑ k ∈ Finset.range n, w (k + 1) * (sg k * drift lam d (s v) (k + 1)), ?_, ?_⟩
    · unfold P
      have h := HasDerivWithinAt.sum (u := Finset.range n)
        (A := fun k y => w (k + 1) * |s y (k + 1) - fixedPoint lam d (k + 1)|)
        (fun k _ => (hsg3 k).const_mul _)
      rw [Finset.sum_fn] at h
      exact h
    · have hfac : ∀ i, s v i ^ d - fixedPoint lam d i ^ d
          = A (s v i) (fixedPoint lam d i) * (s v i - fixedPoint lam d i) ∧
          0 ≤ A (s v i) (fixedPoint lam d i) :=
        fun i => hA _ _ (hx.2.1 i) (st_le_one hx i) (hp0 i) (hp1 i)
      have h := alg n lam δ w (fun i => A (s v i) (fixedPoint lam d i))
        (fun i => s v i - fixedPoint lam d i) sg (fun k => drift lam d (s v) (k + 1))
        hlam0.le hw0 hwnn (fun i => (hfac i).2)
        (by show s v 0 - fixedPoint lam d 0 = 0; rw [hx.1]; simp [fixedPoint]) hsg1 hsg2
        (by
          intro k
          show drift lam d (s v) (k + 1) = lam * (A (s v k) (fixedPoint lam d k) * (s v k - fixedPoint lam d k)
            - A (s v (k + 1)) (fixedPoint lam d (k + 1)) * (s v (k + 1) - fixedPoint lam d (k + 1)))
            - ((s v (k + 1) - fixedPoint lam d (k + 1)) - (s v (k + 1 + 1) - fixedPoint lam d (k + 1 + 1)))
          have h0 := drift_fp lam d (k + 1) (by omega)
          unfold drift at h0 ⊢
          simp only [Nat.add_sub_cancel] at h0 ⊢
          rw [← (hfac k).1, ← (hfac (k + 1)).1]
          linear_combination h0)
        (fun i hi => hcoef (s v) hx i hi)
      unfold P
      linarith [hε v hv]
  · exact le_rfl

end traj2

lemma gb_mono {a a' β β' v t : ℝ} (ha : a ≤ a') (ha0 : 0 ≤ a) (hβ : β ≤ β') (hβ0 : 0 ≤ β)
    (hv : 0 ≤ v) (hvt : v ≤ t) : gronwallBound a 2 β v ≤ gronwallBound a' 2 β' t := by
  simp only [gronwallBound_of_K_ne_0 (two_ne_zero : (2 : ℝ) ≠ 0)]
  have h1 : Real.exp (2 * v) ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 1 ≤ Real.exp (2 * v) := Real.one_le_exp (by linarith)
  have h3 : a * Real.exp (2 * v) ≤ a' * Real.exp (2 * t) :=
    mul_le_mul ha h1 (Real.exp_pos _).le (le_trans ha0 ha)
  have h4 : β * (Real.exp (2 * v) - 1) ≤ β' * (Real.exp (2 * t) - 1) :=
    mul_le_mul hβ (by linarith) (by linarith) (le_trans hβ0 hβ)
  linarith

lemma gb_neg {a ε δ v : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    gronwallBound a (-δ) ε v ≤ a * Real.exp (-δ * v) + ε / δ := by
  simp only [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hδ.ne')]
  have hq : 0 ≤ ε / δ := div_nonneg hε hδ.le
  have he := Real.exp_pos (-δ * v)
  rw [div_neg]
  nlinarith

section main

variable {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}

theorem decay (hlam0 : 0 < lam) (hlam1 : lam < 1) (hd : 2 ≤ d) (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} (hw0 : w 0 = 0) (hw1 : ∀ i, 1 ≤ i → 1 ≤ w i) (hwmono : ∀ i, w i ≤ w (i + 1))
    (hw2 : ∀ i, 1 ≤ i → w (i + 1) ≤ 2 * w i) (hwtop : Tendsto w atTop atTop)
    (hwp : Summable (fun i => w i * fixedPoint lam d i))
    (A : ℝ → ℝ → ℝ) (hA : ∀ x p : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ p → p ≤ 1 →
      x ^ d - p ^ d = A x p * (x - p) ∧ 0 ≤ A x p)
    {δ : ℝ} (hδ : 0 < δ) (hcoef : ∀ x : ℕ → ℝ, IsState x → ∀ i, 1 ≤ i →
      lam * A (x i) (fixedPoint lam d i) * (w (i + 1) - w i) - w i + w (i - 1) ≤ -δ * w i)
    (t : ℝ) (ht : 0 ≤ t) :
    potential lam d w (s t) ≤ ENNReal.ofReal (Real.exp (-δ * t)) * potential lam d w (s 0) := by
  have hwnn : ∀ i, 0 ≤ w i := fun i => by
    rcases i with _ | i
    · rw [hw0]
    · linarith [hw1 (i + 1) (by omega)]
  have hwpos : ∀ n, 1 ≤ n → 0 < w n := fun n hn => by linarith [hw1 n hn]
  have hp0 : ∀ i, 0 ≤ fixedPoint lam d i := fun i => pow_nonneg hlam0.le _
  have hxs : ∀ v, 0 ≤ v → ∀ i, 0 ≤ s v i ∧ s v i ≤ 1 := fun v hv i =>
    ⟨(hs.1 v hv).2.1 i, st_le_one (hs.1 v hv) i⟩
  set g : ℝ → ℕ → ℝ := fun v i => if 1 ≤ i then w i * |s v i - fixedPoint lam d i| else 0
    with hg
  have gnn : ∀ v i, 0 ≤ g v i := fun v i => by
    simp only [hg]; split_ifs
    · exact mul_nonneg (hwnn i) (abs_nonneg _)
    · exact le_rfl
  have hpot : ∀ v, potential lam d w (s v) = ∑' i, ENNReal.ofReal (g v i) := by
    intro v; unfold potential; congr 1; ext i; simp only [hg]; split_ifs <;> simp
  have hPg : ∀ v n, P lam d w s n v = ∑ k ∈ Finset.range n, g v (k + 1) := by
    intro v n; unfold P; apply Finset.sum_congr rfl; intro k _; simp [hg]
  by_cases htop : potential lam d w (s 0) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
    exact le_top
  have hsum0 : Summable (g 0) := by
    apply summable_of_sum_range_le (c := (potential lam d w (s 0)).toReal) (gnn 0)
    intro n
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => gnn 0 i), hpot]
    exact ENNReal.sum_le_tsum _
  set Φ0 := ∑' i, g 0 i with hΦ0def
  have hΦ0 : potential lam d w (s 0) = ENNReal.ofReal Φ0 := by
    rw [hpot, ENNReal.ofReal_tsum_of_nonneg (gnn 0) hsum0]
  have hP0 : ∀ n, P lam d w s n 0 ≤ Φ0 := by
    intro n
    rw [hPg]
    calc ∑ k ∈ Finset.range n, g 0 (k + 1) ≤ ∑ i ∈ Finset.range (n + 1), g 0 i := by
          rw [Finset.sum_range_succ']; linarith [gnn 0 0]
      _ ≤ Φ0 := hsum0.sum_le_tsum _ (fun i _ => gnn 0 i)
  -- a priori bounds
  set xw : ℕ → ℝ := fun i => w i * s 0 i with hxw
  have hxwsum : Summable xw := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hwnn i) (hxs 0 le_rfl i).1)
      (fun i => ?_) (hsum0.add hwp)
    show w i * s 0 i ≤ g 0 i + w i * fixedPoint lam d i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [hg, hw0]
    · have hgi : g 0 i = w i * |s 0 i - fixedPoint lam d i| := by
        simp only [hg]; rw [if_pos (by omega)]
      rw [hgi]
      have := mul_le_mul_of_nonneg_left
        (show s 0 i ≤ |s 0 i - fixedPoint lam d i| + fixedPoint lam d i by
          linarith [le_abs_self (s 0 i - fixedPoint lam d i)]) (hwnn i)
      linarith
  set Tl : ℕ → ℝ := fun n => ∑' k, xw (k + (n + 1)) with hTl
  have hTl0 : Tendsto Tl atTop (𝓝 0) :=
    (tendsto_sum_nat_add xw).comp (tendsto_add_atTop_nat 1)
  have hT0nn : ∀ n m, 0 ≤ T w s n m 0 := fun n m => by
    unfold T; exact Finset.sum_nonneg (fun i _ => mul_nonneg (hwnn _) (hxs 0 le_rfl _).1)
  have hTsum : ∀ n m, T w s n m 0 ≤ Tl n := by
    intro n m
    exact ((summable_nat_add_iff (n + 1)).mpr hxwsum).sum_le_tsum _
      (fun i _ => mul_nonneg (hwnn _) (hxs 0 le_rfl _).1)
  set M := gronwallBound (Tl 0) 2 (lam * w 1) t with hMdef
  have hM : ∀ n, 1 ≤ n → ∀ v ∈ Icc 0 t, w n * s v n ≤ M := by
    intro n hn v hv
    have hTg := T_gron hlam0 hlam1 hs (by omega) hwnn hw2 0 n t (lam * w 1)
      (fun u hu => by rw [(hs.1 u hu.1).1]; simp) v hv
    have h1 : T w s 0 n v ≤ M := le_trans hTg
      (gb_mono (hTsum 0 n) (hT0nn 0 n) le_rfl (mul_nonneg hlam0.le (hwnn 1)) hv.1 hv.2)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h2 : w (n' + 1) * s v (n' + 1) ≤ T w s 0 (n' + 1) v := by
      unfold T; rw [Finset.sum_range_succ]
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range n') =>
        mul_nonneg (hwnn (i + (0 + 1))) (hxs v hv.1 (i + (0 + 1))).1)
      simp only [zero_add] at this ⊢
      linarith
    linarith
  have hM0 : 0 ≤ M :=
    le_trans (mul_nonneg (hwnn 1) (hxs 0 le_rfl 1).1) (hM 1 le_rfl 0 ⟨le_rfl, ht⟩)
  set β : ℕ → ℝ := fun n => lam * w (n + 1) * (M / w n) ^ d with hβdef
  set ε : ℕ → ℝ := fun n => w n * fixedPoint lam d (n + 1) + gronwallBound (Tl n) 2 (β n) t
    with hεdef
  have hβ0 : ∀ n, 0 ≤ β n := fun n =>
    mul_nonneg (mul_nonneg hlam0.le (hwnn _)) (pow_nonneg (div_nonneg hM0 (hwnn n)) d)
  have hεb : ∀ n, 1 ≤ n → ∀ v ∈ Icc 0 t,
      w n * |s v (n + 1) - fixedPoint lam d (n + 1)| ≤ ε n := by
    intro n hn v hv
    have hxv := hxs v hv.1 (n + 1)
    have hab : |s v (n + 1) - fixedPoint lam d (n + 1)| ≤ s v (n + 1) + fixedPoint lam d (n + 1) :=
      abs_sub_le_iff.mpr ⟨by linarith [hp0 (n + 1)], by linarith⟩
    have hTg := T_gron hlam0 hlam1 hs (by omega) hwnn hw2 n 1 t (β n) (fun u hu => by
      have hu' : u ∈ Icc 0 t := ⟨hu.1, hu.2.le⟩
      have h1 := hM n hn u hu'
      have h2 : s u n ≤ M / w n := by rw [le_div_iff₀ (hwpos n hn)]; linarith
      have h3 := pow_le_pow_left₀ (hxs u hu.1 n).1 h2 d
      exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hlam0.le (hwnn _))) v hv
    have h4 : T w s n 1 v ≤ gronwallBound (Tl n) 2 (β n) t :=
      le_trans hTg (gb_mono (hTsum n 1) (hT0nn n 1) le_rfl (hβ0 n) hv.1 hv.2)
    have h5 : T w s n 1 v = w (n + 1) * s v (n + 1) := by simp [T]
    have h6 : w n * s v (n + 1) ≤ w (n + 1) * s v (n + 1) :=
      mul_le_mul_of_nonneg_right (hwmono n) hxv.1
    have h7 := mul_le_mul_of_nonneg_left hab (hwnn n)
    show _ ≤ w n * fixedPoint lam d (n + 1) + gronwallBound (Tl n) 2 (β n) t
    linarith
  have hPn : ∀ n, 1 ≤ n → P lam d w s n t ≤ Real.exp (-δ * t) * Φ0 + ε n / δ := by
    intro n hn
    have hε0 : 0 ≤ ε n :=
      le_trans (mul_nonneg (hwnn n) (abs_nonneg _)) (hεb n hn 0 ⟨le_rfl, ht⟩)
    have h1 := P_gron hlam0 hlam1 hs hw0 hwnn A hA hcoef n t (ε n)
      (fun v hv => hεb n hn v ⟨hv.1, hv.2.le⟩) t ⟨ht, le_rfl⟩
    have h2 := gb_neg (a := P lam d w s n 0) (v := t) hε0 hδ
    have h3 := mul_le_mul_of_nonneg_right (hP0 n) (Real.exp_pos (-δ * t)).le
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hy : Tendsto (fun n => M / w n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hwtop
    obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hyp : Tendsto (fun n => 2 * lam * M * (M / w n) ^ d') atTop (𝓝 0) := by
      have := (hy.pow d').const_mul (2 * lam * M)
      rw [zero_pow (by omega), mul_zero] at this
      exact this
    have hβlim : Tendsto β atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall hβ0) ?_ hyp
      filter_upwards [eventually_ge_atTop 1] with n hn
      show lam * w (n + 1) * (M / w n) ^ d ≤ 2 * lam * M * (M / w n) ^ d'
      have hy0 : 0 ≤ M / w n := div_nonneg hM0 (hwnn n)
      have hwM : w n * (M / w n) = M := mul_div_cancel₀ M (hwpos n hn).ne'
      have h1 : w (n + 1) * (M / w n) ≤ 2 * M := by
        have := mul_le_mul_of_nonneg_right (hw2 n hn) hy0
        linarith [show 2 * w n * (M / w n) = 2 * (w n * (M / w n)) by ring]
      rw [hd', pow_succ]
      have hq := pow_nonneg hy0 d'
      nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hlam0.le hq)]
    have ht1 : Tendsto (fun n => w n * fixedPoint lam d (n + 1)) atTop (𝓝 0) := by
      have := hwp.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
      refine squeeze_zero (fun n => mul_nonneg (hwnn n) (hp0 _)) (fun n => ?_) this
      exact mul_le_mul_of_nonneg_right (hwmono n) (hp0 _)
    have ht2 : Tendsto (fun n => gronwallBound (Tl n) 2 (β n) t) atTop (𝓝 0) := by
      simp only [gronwallBound_of_K_ne_0 (two_ne_zero : (2 : ℝ) ≠ 0)]
      have := (hTl0.mul_const (Real.exp (2 * t))).add
        ((hβlim.div_const 2).mul_const (Real.exp (2 * t) - 1))
      simpa using this
    have := ht1.add ht2
    rw [add_zero] at this
    exact this
  have hmain : ∀ N, P lam d w s N t ≤ Real.exp (-δ * t) * Φ0 := by
    intro N
    have hlim : Tendsto (fun n => Real.exp (-δ * t) * Φ0 + ε n / δ) atTop
        (𝓝 (Real.exp (-δ * t) * Φ0)) := by
      have := (tendsto_const_nhds (x := Real.exp (-δ * t) * Φ0)).add (hεlim.div_const δ)
      rw [zero_div, add_zero] at this
      exact this
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hmono : P lam d w s N t ≤ P lam d w s n t := by
      unfold P
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_of_max_le_left hn))
        (fun i _ _ => mul_nonneg (hwnn _) (abs_nonneg _))
    exact le_trans hmono (hPn n (le_of_max_le_right hn))
  rw [hpot t, hΦ0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => gnn t i)]
  apply ENNReal.ofReal_le_ofReal
  have hgt0 : g t 0 = 0 := by simp [hg]
  calc ∑ i ∈ Finset.range N, g t i ≤ ∑ i ∈ Finset.range (N + 1), g t i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
          (fun i _ _ => gnn t i)
    _ = P lam d w s N t := by rw [Finset.sum_range_succ', hPg, hgt0, add_zero]
    _ ≤ _ := hmain N

end main

end SC77K8B

namespace SC77K8C

open StrictCompatLB.MeanField PowerTwoChoices.Limit SC77K8

section wtfacts

variable {lam q : ℝ} {i0 : ℕ}

lemma W_ge_one (hq0 : 0 < q) (hq : q ≤ 1 / 2) (j : ℕ) (hj : 1 ≤ j) :
    1 ≤ (1 - q ^ j) / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  rw [le_div_iff₀ h1q]
  have : q ^ j ≤ q ^ 1 := pow_le_pow_of_le_one hq0.le (by linarith) hj
  simp at this; linarith

lemma eta_pos (hq0 : 0 < q) (hlam1 : lam < 1) : 0 < q ^ i0 * (1 - lam) / 8 :=
  div_pos (mul_pos (pow_pos hq0 i0) (by linarith)) (by norm_num)

lemma eta_le (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hlam1 : lam < 1) :
    q ^ i0 * (1 - lam) / 8 ≤ (1 - lam) / 8 := by
  have : q ^ i0 ≤ 1 := pow_le_one₀ hq0.le (by linarith)
  have h : 0 < 1 - lam := by linarith
  nlinarith

lemma wt_zero : wt lam q i0 0 = 0 := by simp [wt]

lemma wt_nonneg (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hlam1 : lam < 1) (i : ℕ) :
    0 ≤ wt lam q i0 i := by
  unfold wt
  split_ifs
  · exact (W_bounds hq0.le hq i).1
  · exact mul_nonneg (W_bounds hq0.le hq i0).1
      (pow_nonneg (by linarith [eta_pos (i0 := i0) hq0 hlam1]) _)

lemma wt_succ_tail (hq1 : q < 1) (i : ℕ) (hi : i0 ≤ i) :
    wt lam q i0 (i + 1) = wt lam q i0 i * (1 + q ^ i0 * (1 - lam) / 8) := by
  rw [wt_tail hq1 (i + 1) (by omega), wt_tail hq1 i hi,
    show i + 1 - i0 = (i - i0) + 1 by omega, pow_succ]
  ring

lemma wt_ge_one (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hi0 : 1 ≤ i0) (hlam1 : lam < 1)
    (i : ℕ) (hi : 1 ≤ i) : 1 ≤ wt lam q i0 i := by
  by_cases h : i ≤ i0
  · rw [wt_le i h]; exact W_ge_one hq0 hq i hi
  · rw [wt_tail (by linarith) i (by omega)]
    have hη : 1 ≤ (1 + q ^ i0 * (1 - lam) / 8) ^ (i - i0) :=
      one_le_pow₀ (by linarith [eta_pos (i0 := i0) hq0 hlam1])
    have := W_ge_one hq0 hq i0 hi0
    nlinarith

lemma wt_mono (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hlam1 : lam < 1) (i : ℕ) :
    wt lam q i0 i ≤ wt lam q i0 (i + 1) := by
  have hq1 : q < 1 := by linarith
  by_cases h : i + 1 ≤ i0
  · rw [wt_le (i + 1) h, wt_le i (by omega)]
    have := wt_step hq1 i
    have := pow_nonneg hq0.le i
    linarith
  · rw [wt_succ_tail hq1 i (by omega)]
    have := wt_nonneg (i0 := i0) hq0 hq hlam1 i
    have := eta_pos (i0 := i0) hq0 hlam1
    nlinarith

lemma wt_two (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hi0 : 1 ≤ i0) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (i : ℕ) (hi : 1 ≤ i) : wt lam q i0 (i + 1) ≤ 2 * wt lam q i0 i := by
  have hq1 : q < 1 := by linarith
  have hge := wt_ge_one hq0 hq hi0 hlam1 i hi
  by_cases h : i + 1 ≤ i0
  · have e1 := wt_le (lam := lam) (q := q) (i + 1) h
    have e2 := wt_le (lam := lam) (q := q) i (by omega : i ≤ i0)
    have := wt_step hq1 i
    have : q ^ i ≤ 1 := pow_le_one₀ hq0.le (by linarith)
    rw [e1]; rw [e2] at hge ⊢
    linarith
  · rw [wt_succ_tail hq1 i (by omega)]
    have := eta_le (i0 := i0) hq0 hq hlam1
    have := wt_nonneg (i0 := i0) hq0 hq hlam1 i
    nlinarith

lemma wt_le_geom (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hlam1 : lam < 1) (i : ℕ) :
    wt lam q i0 i ≤ 2 * (1 + q ^ i0 * (1 - lam) / 8) ^ i := by
  have hq1 : q < 1 := by linarith
  have h1η : 1 ≤ 1 + q ^ i0 * (1 - lam) / 8 := by linarith [eta_pos (i0 := i0) hq0 hlam1]
  by_cases h : i ≤ i0
  · rw [wt_le i h]
    have := (W_bounds hq0.le hq i).2
    have : 1 ≤ (1 + q ^ i0 * (1 - lam) / 8) ^ i := one_le_pow₀ h1η
    linarith
  · rw [wt_tail hq1 i (by omega)]
    have hW := W_bounds hq0.le hq i0
    have hp : (1 + q ^ i0 * (1 - lam) / 8) ^ (i - i0) ≤ (1 + q ^ i0 * (1 - lam) / 8) ^ i :=
      pow_le_pow_right₀ h1η (Nat.sub_le i i0)
    exact mul_le_mul hW.2 hp (pow_nonneg (by linarith) _) (by norm_num)

lemma wt_top (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hi0 : 1 ≤ i0) (hlam1 : lam < 1) :
    Tendsto (wt lam q i0) atTop atTop := by
  have hq1 : q < 1 := by linarith
  have hW : 0 < (1 - q ^ i0) / (1 - q) := by linarith [W_ge_one hq0 hq i0 hi0]
  have h1 : Tendsto (fun i => (1 - q ^ i0) / (1 - q) * (1 + q ^ i0 * (1 - lam) / 8) ^ (i - i0))
      atTop atTop :=
    Tendsto.const_mul_atTop hW ((tendsto_pow_atTop_atTop_of_one_lt
      (by linarith [eta_pos (i0 := i0) hq0 hlam1])).comp (tendsto_sub_atTop_nat i0))
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop i0] with i hi
  exact (wt_tail hq1 i hi).symm

end wtfacts

theorem k8 : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
    ∃ ω : ℕ → ℝ, (∀ i, 1 ≤ i → 0 < ω i) ∧ ∃ r : ℝ, 1 < r ∧ r < 2 / (1 + lam) ∧
      (∀ i : ℕ, 1 ≤ i → ω (i0Index lam d + i) = ω (i0Index lam d) * r ^ i) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → ∀ t : ℝ, 0 ≤ t →
          PowerTwoChoices.Limit.potential lam d ω (s t) ≤
            ENNReal.ofReal (Real.exp (-δ * t)) * PowerTwoChoices.Limit.potential lam d ω (s 0) := by
  intro lam hlam0 hlam1 d hd
  obtain ⟨hi0, hfa, hfb⟩ := i0_facts lam hlam0 hlam1 d hd
  set i0 := i0Index lam d with hi0def
  have hld : 0 ≤ lam * d := mul_nonneg hlam0.le (Nat.cast_nonneg d)
  set q : ℝ := 1 / (2 * (lam * d + 1)) with hqdef
  have hq0 : 0 < q := div_pos one_pos (by linarith)
  have hq : q ≤ 1 / 2 := by
    rw [hqdef, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hqd : lam * d * q ≤ 1 / 2 := by
    rw [hqdef, mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hq1 : q < 1 := by linarith
  have hη0 := eta_pos (i0 := i0) hq0 hlam1
  have hη1 := eta_le (i0 := i0) hq0 hq hlam1
  refine ⟨wt lam q i0, fun i hi => lt_of_lt_of_le one_pos (wt_ge_one hq0 hq hi0 hlam1 i hi),
    1 + q ^ i0 * (1 - lam) / 8, by linarith, ?_, ?_,
    q ^ i0 * (1 - lam) / 8 * (1 - lam) / 4, ?_, ?_⟩
  · rw [lt_div_iff₀ (by linarith)]
    nlinarith
  · intro i _
    rw [wt_tail hq1 (i0 + i) (by omega), wt_tail hq1 i0 le_rfl]
    simp
  · exact div_pos (mul_pos hη0 (by linarith)) (by norm_num)
  · intro s hs _ t ht
    have hρ1 : (1 + q ^ i0 * (1 - lam) / 8) * lam < 1 := by nlinarith
    have hρ0 : 0 ≤ (1 + q ^ i0 * (1 - lam) / 8) * lam := by nlinarith
    have hsum : Summable (fun i => wt lam q i0 i * PowerTwoChoices.Limit.fixedPoint lam d i) := by
      refine Summable.of_nonneg_of_le
        (fun i => mul_nonneg (wt_nonneg hq0 hq hlam1 i) (fp_nonneg lam hlam0.le d i))
        (fun i => ?_) ((summable_geometric_of_lt_one hρ0 hρ1).mul_left 2)
      have h1 := wt_le_geom (i0 := i0) hq0 hq hlam1 i
      have h2 := fp_le_pow lam hlam0.le hlam1.le d (by omega) i
      calc wt lam q i0 i * PowerTwoChoices.Limit.fixedPoint lam d i
          ≤ (2 * (1 + q ^ i0 * (1 - lam) / 8) ^ i) * lam ^ i :=
            mul_le_mul h1 h2 (fp_nonneg lam hlam0.le d i)
              (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
        _ = 2 * ((1 + q ^ i0 * (1 - lam) / 8) * lam) ^ i := by rw [mul_pow]; ring
    refine SC77K8B.decay hlam0 hlam1 hd hs wt_zero (wt_ge_one hq0 hq hi0 hlam1)
      (wt_mono hq0 hq hlam1) (wt_two hq0 hq hi0 hlam0 hlam1) (wt_top hq0 hq hi0 hlam1) hsum
      (fun x p => ∑ k ∈ Finset.range d, x ^ k * p ^ (d - 1 - k))
      (fun x p hx0 hx1 hp0 hp1 => by
        have h := a_facts x p hx0 hx1 hp0 hp1 d
        exact ⟨h.1, h.2.1⟩)
      (div_pos (mul_pos hη0 (by linarith)) (by norm_num)) ?_ t ht
    intro x hx i hi
    have hxi0 := hx.2.1 i
    have hxi1 := SC77K8B.st_le_one hx i
    have hp0 := fp_nonneg lam hlam0.le d i
    have hp1 : PowerTwoChoices.Limit.fixedPoint lam d i ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
    have h := a_facts (x i) (PowerTwoChoices.Limit.fixedPoint lam d i) hxi0 hxi1 hp0 hp1 d
    exact coef_le hlam0 hlam1 d hq0 hq hqd hi0 i hi _ h.2.1 h.2.2.1 (fun hii => by
      have hg := geom_bound (PowerTwoChoices.Limit.fixedPoint lam d i) hp0 (hfb i hii) d
      have hf := hfa i hii
      have h4 := h.2.2.2
      have h5 := mul_le_mul_of_nonneg_left (le_trans h4 hg) hlam0.le
      linarith)

end SC77K8C

open StrictCompatLB.MeanField in
theorem solution : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∃ ω : ℕ → ℝ, (∀ i, 1 ≤ i → 0 < ω i) ∧ ∃ r : ℝ, 1 < r ∧ r < 2 / (1 + lam) ∧
    (∀ i : ℕ, 1 ≤ i → ω (i0Index lam d + i) = ω (i0Index lam d) * r ^ i) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
      (∀ t : ℝ, 0 ≤ t → InY (s t)) → ∀ t : ℝ, 0 ≤ t →
        PowerTwoChoices.Limit.potential lam d ω (s t) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) * PowerTwoChoices.Limit.potential lam d ω (s 0) := by
  exact SC77K8C.k8
