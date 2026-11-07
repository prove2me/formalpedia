-- Prove2me | solution 1 for PriceSwitch.UpOrDown.theorem3_markup_or_markdown_thresholds
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:09:16.867102+00:00
-- url     : https://prove2.me/submissions/dd3b6139-a9bf-455c-bdd9-cc5076e0c5cc

import Mathlib
import Definitions.Def_PriceSwitch_UpOrDown_ThreePrice

set_option autoImplicit false

open PriceSwitch.Markdown
open Filter Topology

namespace DP3L3

open Nat

noncomputable def FF (n : ℕ) (m : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.exp (-m) * m ^ k / (k ! : ℝ)

lemma hasDerivAt_FF (n : ℕ) (m : ℝ) :
    HasDerivAt (FF (n + 1)) (-(Real.exp (-m) * m ^ n / (n ! : ℝ))) m := by
  induction n with
  | zero =>
    have h : FF 1 = fun m => Real.exp (-m) := by funext m; simp [FF]
    rw [h]
    have := (Real.hasDerivAt_exp (-m)).comp m (hasDerivAt_neg m)
    refine this.congr_deriv ?_
    simp
  | succ n ih =>
    have h : FF (n + 1 + 1) = fun m => FF (n + 1) m + Real.exp (-m) * m ^ (n + 1) / ((n + 1) ! : ℝ) := by
      funext m; simp [FF, Finset.sum_range_succ _ (n + 1)]
    rw [h]
    have h1 : HasDerivAt (fun m : ℝ => Real.exp (-m)) (-Real.exp (-m)) m := by
      have := (Real.hasDerivAt_exp (-m)).comp m (hasDerivAt_neg m)
      exact this.congr_deriv (by simp)
    have h2 := ((h1.mul (hasDerivAt_pow (n + 1) m)).div_const ((n + 1) ! : ℝ))
    refine (ih.add h2).congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have : (n ! : ℝ) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma FF_zero_succ (n : ℕ) : FF (n + 1) 0 = 1 := by
  simp [FF, Finset.sum_range_succ', zero_pow_eq]

lemma FF_cont (n : ℕ) : Continuous (FF (n + 1)) :=
  continuous_iff_continuousAt.2 fun m => (hasDerivAt_FF n m).continuousAt

lemma FF_anti (n : ℕ) : StrictAntiOn (FF (n + 1)) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (FF_cont n).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : (0:ℝ) < x := hx
  rw [(hasDerivAt_FF n x).deriv]
  have : 0 < Real.exp (-x) * x ^ n / (n ! : ℝ) := by positivity
  linarith

lemma FF_succ_sub (n : ℕ) (m : ℝ) :
    FF (n + 1 + 1) m - FF (n + 1) m = Real.exp (-m) * m ^ (n + 1) / ((n + 1) ! : ℝ) := by
  simp [FF, Finset.sum_range_succ _ (n + 1)]

lemma FF_tendsto (n : ℕ) : Filter.Tendsto (FF (n + 1)) Filter.atTop (nhds 0) := by
  unfold FF
  have : ∀ k ∈ Finset.range (n + 1), Filter.Tendsto (fun m : ℝ => Real.exp (-m) * m ^ k / (k ! : ℝ))
      Filter.atTop (nhds 0) := by
    intro k _
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div_const (k ! : ℝ)
    simp only [zero_div] at this
    refine this.congr fun m => ?_
    ring
  simpa using tendsto_finsetSum _ this


lemma FF_succ (n : ℕ) (m : ℝ) : FF (n + 1) m = FF n m + Real.exp (-m) * m ^ n / (n ! : ℝ) := by
  simp [FF, Finset.sum_range_succ]

lemma FF_zero_zero : ∀ m : ℝ, FF 0 m = 0 := by intro m; simp [FF]

noncomputable def Tl (k : ℕ) (m : ℝ) : ℝ := 1 - FF k m

lemma Tl_hasDerivAt (k : ℕ) (m : ℝ) :
    HasDerivAt (Tl (k + 1)) (Real.exp (-m) * m ^ k / (k ! : ℝ)) m := by
  have := (hasDerivAt_const m (1 : ℝ)).sub (hasDerivAt_FF k m)
  refine (this.congr_deriv ?_)
  ring

lemma Tl_zero (k : ℕ) : Tl (k + 1) 0 = 0 := by
  simp [Tl, FF_zero_succ]

lemma Tl_pos (k : ℕ) (m : ℝ) (hm : 0 < m) : 0 < Tl (k + 1) m := by
  have := FF_anti k (Set.mem_Ici.2 (le_refl (0:ℝ))) (show m ∈ Set.Ici 0 from hm.le) hm
  rw [FF_zero_succ] at this
  unfold Tl; linarith

noncomputable def Eg (n : ℕ) (m : ℝ) : ℝ := ∑ j ∈ Finset.Icc 1 n, Tl j m

lemma Eg_succ (n : ℕ) (m : ℝ) : Eg (n + 1) m = Eg n m + Tl (n + 1) m := by
  unfold Eg
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma Eg_hasDerivAt (n : ℕ) (m : ℝ) : HasDerivAt (Eg n) (FF n m) m := by
  induction n with
  | zero =>
    have : Eg 0 = fun _ => 0 := by funext x; simp [Eg]
    rw [this, FF_zero_zero]
    exact hasDerivAt_const m 0
  | succ n ih =>
    have h : Eg (n + 1) = fun m => Eg n m + Tl (n + 1) m := by
      funext x; exact Eg_succ n x
    rw [h]
    refine (ih.add (Tl_hasDerivAt n m)).congr_deriv ?_
    rw [FF_succ]

lemma Eg_zero (n : ℕ) : Eg n 0 = 0 := by
  unfold Eg
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
  exact Tl_zero k

lemma Eg_cont (n : ℕ) : Continuous (Eg n) :=
  continuous_iff_continuousAt.2 fun m => (Eg_hasDerivAt n m).continuousAt

lemma Eg_tendsto (n : ℕ) : Filter.Tendsto (Eg n) Filter.atTop (nhds (n : ℝ)) := by
  unfold Eg Tl
  have : ∀ j ∈ Finset.Icc 1 n, Filter.Tendsto (fun m : ℝ => 1 - FF j m) Filter.atTop (nhds 1) := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
    simpa using (FF_tendsto k).const_sub 1
  have := tendsto_finsetSum _ this
  simpa using this

lemma poissonTail_eq (m : ℝ) (j : ℕ) : poissonTail m j = Tl j (max m 0) := by
  unfold poissonTail Tl FF
  have h : ((m.toNNReal : NNReal) : ℝ) = max m 0 := Real.coe_toNNReal'  m
  simp only [ProbabilityTheory.poissonPMFReal, h]

lemma expMin_eq (n : ℕ) (m : ℝ) : expMinPoisson n m = Eg n (max m 0) := by
  unfold expMinPoisson Eg
  exact Finset.sum_congr rfl fun j _ => poissonTail_eq m j

lemma expMin_zero (n : ℕ) : expMinPoisson n 0 = 0 := by
  rw [expMin_eq]; simp [Eg_zero]

lemma expMin_of_nonneg (n : ℕ) (m : ℝ) (hm : 0 ≤ m) : expMinPoisson n m = Eg n m := by
  rw [expMin_eq, max_eq_left hm]

lemma Delta_eq (a la b lb : ℝ) (n : ℕ) (t : ℝ) :
    switchRevenue a la b lb n t t - switchRevenue a la b lb n t 0 =
      a * expMinPoisson n (la * t) - b * expMinPoisson n (lb * t) := by
  unfold switchRevenue
  simp only [sub_self, mul_zero, add_zero, zero_add, sub_zero, expMin_zero]
  ring


lemma Tl_ratio_bound (k : ℕ) (m : ℝ) (hm : 0 < m) :
    Tl (k + 2) m < m / ((k : ℝ) + 1) * Tl (k + 1) m := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x / ((k : ℝ) + 1) * Tl (k + 1) x - Tl (k + 2) x)
      (Tl (k + 1) x / ((k : ℝ) + 1)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x / ((k : ℝ) + 1)) (1 / ((k : ℝ) + 1)) x :=
      (hasDerivAt_id x).div_const _
    have := (h1.mul (Tl_hasDerivAt k x)).sub (Tl_hasDerivAt (k + 1) x)
    refine this.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have : (k ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hcont : ContinuousOn (fun x => x / ((k : ℝ) + 1) * Tl (k + 1) x - Tl (k + 2) x) (Set.Ici 0) :=
    fun x _ => (hd x).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (fun x => x / ((k : ℝ) + 1) * Tl (k + 1) x - Tl (k + 2) x) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have := Tl_pos k x hx
    positivity
  have h0 := hmono (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hm.le) hm
  simp only [Tl_zero, mul_zero, sub_zero] at h0
  linarith

lemma Tl_cross (k : ℕ) (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    Tl (k + 2) x * Tl (k + 1) y < Tl (k + 2) y * Tl (k + 1) x := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hd : ∀ z : ℝ, HasDerivAt (fun z => Tl (k + 2) z * Tl (k + 1) x - Tl (k + 2) x * Tl (k + 1) z)
      (Real.exp (-z) * z ^ (k + 1) / ((k + 1) ! : ℝ) * Tl (k + 1) x
        - Tl (k + 2) x * (Real.exp (-z) * z ^ k / (k ! : ℝ))) z := by
    intro z
    exact (((Tl_hasDerivAt (k + 1) z).mul_const _).sub ((hasDerivAt_const z _).mul (Tl_hasDerivAt k z))).congr_deriv (by ring)
  have hcont : ContinuousOn (fun z => Tl (k + 2) z * Tl (k + 1) x - Tl (k + 2) x * Tl (k + 1) z) (Set.Ici x) :=
    fun z _ => (hd z).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (fun z => Tl (k + 2) z * Tl (k + 1) x - Tl (k + 2) x * Tl (k + 1) z) (Set.Ici x) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x) hcont
    intro z hz
    rw [interior_Ici] at hz
    have hz' : x < z := hz
    rw [(hd z).deriv]
    have hb := Tl_ratio_bound k x hx
    have hz0 : 0 < z := hx.trans hz'
    have hT := Tl_pos k x hx
    have e1 : Real.exp (-z) * z ^ (k + 1) / ((k + 1) ! : ℝ)
        = z / ((k : ℝ) + 1) * (Real.exp (-z) * z ^ k / (k ! : ℝ)) := by
      rw [Nat.factorial_succ]; push_cast
      have : (k ! : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [e1]
    have hg : 0 < Real.exp (-z) * z ^ k / (k ! : ℝ) := by positivity
    have h2 : x / ((k : ℝ) + 1) * Tl (k + 1) x < z / ((k : ℝ) + 1) * Tl (k + 1) x := by
      apply mul_lt_mul_of_pos_right _ hT
      exact div_lt_div_of_pos_right hz' hk
    have h3 : Tl (k + 2) x < z / ((k : ℝ) + 1) * Tl (k + 1) x := by linarith
    nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hxy.le) hxy
  simp only at this
  linarith

lemma Tl_chain (j : ℕ) (hj : 1 ≤ j) (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    ∀ n : ℕ, j ≤ n → Tl (n + 1) x * Tl j y < Tl (n + 1) y * Tl j x := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact Tl_cross k x y hx hxy
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hc : Tl (k + 1 + 1 + 1) x * Tl (k + 1 + 1) y < Tl (k + 1 + 1 + 1) y * Tl (k + 1 + 1) x :=
      Tl_cross (k + 1) x y hx hxy
    have hy : 0 < y := hx.trans hxy
    have hD := Tl_pos k y hy
    have hD' := Tl_pos (k + 1) y hy
    have hF := Tl_pos i y hy
    have hA := Tl_pos (k + 1) x hx
    have hE := Tl_pos i x hx
    have hC := Tl_pos k x hx
    have hB := Tl_pos (k + 1) y hy
    -- A = Tl (k+3) x ; B = Tl (k+3) y ; C = Tl (k+2) x ; D = Tl (k+2) y
    have key : Tl (k + 1 + 1 + 1) x * Tl (k + 1 + 1) y * Tl (i + 1) y
        < Tl (k + 1 + 1 + 1) y * Tl (k + 1 + 1) x * Tl (i + 1) y := by
      exact mul_lt_mul_of_pos_right hc (Tl_pos i y hy)
    have key2 : Tl (k + 1 + 1 + 1) y * (Tl (k + 1 + 1) x * Tl (i + 1) y)
        < Tl (k + 1 + 1 + 1) y * (Tl (k + 1 + 1) y * Tl (i + 1) x) := by
      apply mul_lt_mul_of_pos_left ih
      exact Tl_pos (k + 2) y hy
    have hD2 : 0 < Tl (k + 1 + 1) y := Tl_pos (k + 1) y hy
    have : Tl (k + 1 + 1) y * (Tl (k + 1 + 1 + 1) x * Tl (i + 1) y)
        < Tl (k + 1 + 1) y * (Tl (k + 1 + 1 + 1) y * Tl (i + 1) x) := by nlinarith
    exact lt_of_mul_lt_mul_left this hD2.le

lemma Eg_pos (n : ℕ) (hn : 1 ≤ n) (m : ℝ) (hm : 0 < m) : 0 < Eg n m := by
  unfold Eg
  apply Finset.sum_pos
  · intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
    exact Tl_pos k m hm
  · exact ⟨1, Finset.mem_Icc.2 ⟨le_refl _, hn⟩⟩

lemma Eg_cross (n : ℕ) (hn : 1 ≤ n) (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    Tl (n + 1) x * Eg n y < Tl (n + 1) y * Eg n x := by
  unfold Eg
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_lt_sum_of_nonempty ⟨1, Finset.mem_Icc.2 ⟨le_refl _, hn⟩⟩
  intro j hj
  have hj' := Finset.mem_Icc.1 hj
  exact Tl_chain j hj'.1 x y hx hxy n hj'.2

lemma Tl_next_lt (n : ℕ) (hn : 1 ≤ n) (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hxy : x < y)
    (h : a * Eg n x ≤ b * Eg n y) : a * Tl (n + 1) x < b * Tl (n + 1) y := by
  have hy : 0 < y := hx.trans hxy
  have hc := Eg_cross n hn x y hx hxy
  have hEy := Eg_pos n hn y hy
  have hTy : 0 < Tl (n + 1) y := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact Tl_pos (k + 1) y hy
  have h1 : a * (Tl (n + 1) x * Eg n y) < a * (Tl (n + 1) y * Eg n x) := mul_lt_mul_of_pos_left hc ha
  have h2 : Tl (n + 1) y * (a * Eg n x) ≤ Tl (n + 1) y * (b * Eg n y) := mul_le_mul_of_nonneg_left h hTy.le
  have h3 : (a * Tl (n + 1) x) * Eg n y < (b * Tl (n + 1) y) * Eg n y := by nlinarith
  exact lt_of_mul_lt_mul_right h3 hEy.le


noncomputable def PP (k : ℕ) (m : ℝ) : ℝ := ∑ i ∈ Finset.range (k + 1), m ^ i / (i ! : ℝ)

lemma FF_eq_PP (k : ℕ) (m : ℝ) : FF (k + 1) m = Real.exp (-m) * PP k m := by
  unfold FF PP
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma PP_cross (k : ℕ) (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    x ^ (k + 1) * PP k y < y ^ (k + 1) * PP k x := by
  unfold PP
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 (by omega)⟩
  intro i hi
  have hi' := Finset.mem_range.1 hi
  obtain ⟨d, hd⟩ : ∃ d, k + 1 = i + (d + 1) := ⟨k - i, by omega⟩
  have hy : 0 < y := hx.trans hxy
  have h1 : x ^ (d + 1) < y ^ (d + 1) := pow_lt_pow_left₀ hxy hx.le (by omega)
  have h2 : 0 < x ^ i * y ^ i := by positivity
  have h3 : x ^ (k + 1) * y ^ i < y ^ (k + 1) * x ^ i := by
    have e1 : x ^ (k + 1) * y ^ i = (x ^ i * y ^ i) * x ^ (d + 1) := by rw [hd]; ring
    have e2 : y ^ (k + 1) * x ^ i = (x ^ i * y ^ i) * y ^ (d + 1) := by rw [hd]; ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left h1 h2
  have hf : (0 : ℝ) < (i ! : ℝ) := by positivity
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact div_lt_div_of_pos_right h3 hf

lemma FF_comp_hasDerivAt (k : ℕ) (c t : ℝ) :
    HasDerivAt (fun t => FF (k + 1) (c * t)) (-(Real.exp (-(c * t)) * (c * t) ^ k / (k ! : ℝ)) * c) t := by
  have := (hasDerivAt_FF k (c * t)).comp t ((hasDerivAt_id t).const_mul c)
  exact this.congr_deriv (by simp)

lemma FF_pos (k : ℕ) (m : ℝ) (hm : 0 ≤ m) : 0 < FF (k + 1) m := by
  rw [FF_eq_PP]
  unfold PP
  have : 0 < ∑ i ∈ Finset.range (k + 1), m ^ i / (i ! : ℝ) := by
    apply Finset.sum_pos'
    · intro i _; positivity
    · exact ⟨0, Finset.mem_range.2 (by omega), by simp⟩
  positivity

lemma ratio_strictMono (k : ℕ) (la lb : ℝ) (hla : 0 < la) (hll : la < lb) :
    StrictMonoOn (fun t => FF (k + 1) (la * t) / FF (k + 1) (lb * t)) (Set.Ioi 0) := by
  have hlb : 0 < lb := hla.trans hll
  have hv : ∀ t : ℝ, 0 < t → FF (k + 1) (lb * t) ≠ 0 := fun t ht => (FF_pos k _ (by positivity)).ne'
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => FF (k + 1) (la * t) / FF (k + 1) (lb * t))
      (((-(Real.exp (-(la * t)) * (la * t) ^ k / (k ! : ℝ)) * la) * FF (k + 1) (lb * t)
        - FF (k + 1) (la * t) * (-(Real.exp (-(lb * t)) * (lb * t) ^ k / (k ! : ℝ)) * lb))
        / FF (k + 1) (lb * t) ^ 2) t :=
    fun t ht => (FF_comp_hasDerivAt k la t).div (FF_comp_hasDerivAt k lb t) (hv t ht)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    have ht' : 0 < t := ht
    rw [(hd t ht').deriv]
    apply _root_.div_pos _ (by have := FF_pos k (lb * t) (by positivity); positivity)
    have hK := PP_cross k (la * t) (lb * t) (by positivity) (by nlinarith)
    rw [FF_eq_PP, FF_eq_PP]
    have hE : 0 < Real.exp (-(la * t)) * Real.exp (-(lb * t)) / (k ! : ℝ) := by positivity
    have hS : 0 < lb * (lb * t) ^ k * PP k (la * t) - la * (la * t) ^ k * PP k (lb * t) := by
      have : t * (lb * (lb * t) ^ k * PP k (la * t) - la * (la * t) ^ k * PP k (lb * t))
          = (lb * t) ^ (k + 1) * PP k (la * t) - (la * t) ^ (k + 1) * PP k (lb * t) := by ring
      have h2 : 0 < t * (lb * (lb * t) ^ k * PP k (la * t) - la * (la * t) ^ k * PP k (lb * t)) := by
        rw [this]; linarith
      exact (mul_pos_iff_of_pos_left ht').1 h2
    have := mul_pos hE hS
    convert this using 1
    ring

lemma persist (k : ℕ) (a la b lb : ℝ) (ha : 0 < a) (hb : 0 < b) (hla : 0 < la) (hll : la < lb)
    (s t : ℝ) (hs : 0 < s) (hst : s < t)
    (h : b * lb * FF (k + 1) (lb * s) ≤ a * la * FF (k + 1) (la * s)) :
    b * lb * FF (k + 1) (lb * t) < a * la * FF (k + 1) (la * t) := by
  have hlb : 0 < lb := hla.trans hll
  have hR := ratio_strictMono k la lb hla hll (Set.mem_Ioi.2 hs) (Set.mem_Ioi.2 (hs.trans hst)) hst
  simp only at hR
  have hvs := FF_pos k (lb * s) (by positivity)
  have hvt := FF_pos k (lb * t) (by have := hs.trans hst; positivity)
  rw [div_lt_div_iff₀ hvs hvt] at hR
  -- hR : FF(la s) * FF(lb t) < FF(la t) * FF(lb s)
  have hal : 0 < a * la := mul_pos ha hla
  have hbl : 0 < b * lb := mul_pos hb hlb
  have h1 : b * lb * FF (k + 1) (lb * s) * FF (k + 1) (lb * t) ≤ a * la * FF (k + 1) (la * s) * FF (k + 1) (lb * t) :=
    mul_le_mul_of_nonneg_right h hvt.le
  have h2 : a * la * (FF (k + 1) (la * s) * FF (k + 1) (lb * t)) < a * la * (FF (k + 1) (la * t) * FF (k + 1) (lb * s)) :=
    mul_lt_mul_of_pos_left hR hal
  have h3 : (b * lb * FF (k + 1) (lb * t)) * FF (k + 1) (lb * s) < (a * la * FF (k + 1) (la * t)) * FF (k + 1) (lb * s) := by
    nlinarith
  exact lt_of_mul_lt_mul_right h3 hvs.le


noncomputable def FD (a la b lb : ℝ) (n : ℕ) (t : ℝ) : ℝ := a * Eg n (la * t) - b * Eg n (lb * t)

lemma Eg_comp_hasDerivAt (n : ℕ) (c t : ℝ) :
    HasDerivAt (fun t => Eg n (c * t)) (FF n (c * t) * c) t := by
  have := (Eg_hasDerivAt n (c * t)).comp t ((hasDerivAt_id t).const_mul c)
  exact this.congr_deriv (by simp)

lemma FD_hasDerivAt (a la b lb : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (FD a la b lb n) (a * (FF n (la * t) * la) - b * (FF n (lb * t) * lb)) t :=
  ((Eg_comp_hasDerivAt n la t).const_mul a).sub ((Eg_comp_hasDerivAt n lb t).const_mul b)

lemma FD_zero (a la b lb : ℝ) (n : ℕ) : FD a la b lb n 0 = 0 := by
  simp [FD, Eg_zero]

lemma FD_tendsto (a la b lb : ℝ) (n : ℕ) (hla : 0 < la) (hlb : 0 < lb) :
    Filter.Tendsto (FD a la b lb n) Filter.atTop (nhds ((a - b) * n)) := by
  have h1 : Filter.Tendsto (fun t : ℝ => Eg n (la * t)) Filter.atTop (nhds n) :=
    (Eg_tendsto n).comp (Filter.tendsto_id.const_mul_atTop hla)
  have h2 : Filter.Tendsto (fun t : ℝ => Eg n (lb * t)) Filter.atTop (nhds n) :=
    (Eg_tendsto n).comp (Filter.tendsto_id.const_mul_atTop hlb)
  have := (h1.const_mul a).sub (h2.const_mul b)
  have e : a * (n : ℝ) - b * n = (a - b) * n := by ring
  rw [e] at this
  exact this

lemma FD_struct (a la b lb : ℝ) (ha : 0 < a) (hb : 0 < b) (hla : 0 < la) (hll : la < lb)
    (hab : b < a) (hr : a * la < b * lb) (k : ℕ) :
    ∃ z : ℝ, 0 < z ∧ FD a la b lb (k + 1) z = 0 ∧
      (∀ t, 0 < t → t < z → FD a la b lb (k + 1) t < 0) ∧
      (∀ t, z < t → 0 < FD a la b lb (k + 1) t) ∧
      StrictMonoOn (FD a la b lb (k + 1)) (Set.Ici z) := by
  have hlb : 0 < lb := hla.trans hll
  have hcont : Continuous (FD a la b lb (k + 1)) :=
    continuous_iff_continuousAt.2 fun t => (FD_hasDerivAt a la b lb (k + 1) t).continuousAt
  have K : ∀ t₀ : ℝ, 0 < t₀ → 0 ≤ FD a la b lb (k + 1) t₀ →
      StrictMonoOn (FD a la b lb (k + 1)) (Set.Ici t₀) := by
    intro t₀ ht₀ hf
    obtain ⟨s, hs0, hst, hs⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ t₀ ∧
        0 ≤ a * (FF (k + 1) (la * s) * la) - b * (FF (k + 1) (lb * s) * lb) := by
      by_contra hcon
      push_neg at hcon
      have hanti : StrictAntiOn (FD a la b lb (k + 1)) (Set.Icc 0 t₀) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc 0 t₀) hcont.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [(FD_hasDerivAt a la b lb (k + 1) x).deriv]
        exact hcon x hx.1 hx.2.le
      have := hanti (Set.left_mem_Icc.2 ht₀.le) (Set.right_mem_Icc.2 ht₀.le) ht₀
      rw [FD_zero] at this
      linarith
    have hmono : StrictMonoOn (FD a la b lb (k + 1)) (Set.Ici s) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici s) hcont.continuousOn
      intro x hx
      rw [interior_Ici] at hx
      have hx' : s < x := hx
      rw [(FD_hasDerivAt a la b lb (k + 1) x).deriv]
      have := persist k a la b lb ha hb hla hll s x hs0 hx' (by nlinarith [hs])
      nlinarith [this]
    exact hmono.mono (Set.Ici_subset_Ici.2 hst)
  -- negative values near 0
  obtain ⟨t₂, ht₂, hf₂⟩ : ∃ t₂ : ℝ, 0 < t₂ ∧ FD a la b lb (k + 1) t₂ < 0 := by
    have hd0 : HasDerivAt (FD a la b lb (k + 1)) (a * la - b * lb) 0 := by
      refine (FD_hasDerivAt a la b lb (k + 1) 0).congr_deriv ?_
      simp [FF_zero_succ]
    have hs := hd0.tendsto_slope_zero_right
    have hev := Filter.Tendsto.eventually_lt_const (show a * la - b * lb < 0 - 0 + 0 by nlinarith) hs
    obtain ⟨t, h1, h2⟩ := (hev.and self_mem_nhdsWithin).exists
    have h2' : (0 : ℝ) < t := h2
    refine ⟨t, h2', ?_⟩
    by_contra hcon
    push_neg at hcon
    simp only [zero_add, FD_zero, sub_zero, smul_eq_mul] at h1
    have := mul_nonneg (inv_nonneg.2 h2'.le) hcon
    linarith
  obtain ⟨t₁, h1, h1'⟩ : ∃ t₁ : ℝ, 0 < FD a la b lb (k + 1) t₁ ∧ t₂ < t₁ := by
    have hlim := FD_tendsto a la b lb (k + 1) hla hlb
    have hpos : (0 : ℝ) < (a - b) * ((k + 1 : ℕ) : ℝ) := by
      apply mul_pos (by linarith); positivity
    have := (hlim.eventually_const_lt hpos).and (Filter.eventually_gt_atTop t₂)
    obtain ⟨t, h⟩ := this.exists
    exact ⟨t, h.1, h.2⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc h1'.le hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (FD a la b lb (k + 1) t₂) (FD a la b lb (k + 1) t₁) from ⟨hf₂.le, h1.le⟩)
  have hzpos : 0 < z := ht₂.trans_le hz.1
  have hmono := K z hzpos (by rw [hz0])
  refine ⟨z, hzpos, hz0, ?_, ?_, hmono⟩
  · intro t ht htz
    by_contra hcon
    push_neg at hcon
    have hm := K t ht hcon
    have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 htz.le) htz
    linarith
  · intro t htz
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 htz.le) htz
    linarith


lemma Delta_key (a la b lb : ℝ) (ha : 0 < a) (hb : 0 < b) (hla : 0 < la) (hll : la < lb)
    (hab : b < a) (hr : a * la < b * lb) (Δ : ℕ → ℝ → ℝ)
    (hΔ : ∀ n t, Δ n t = a * expMinPoisson n (la * t) - b * expMinPoisson n (lb * t))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℝ, 0 < z ∧ Δ n z = 0 ∧ (∀ t, 0 < t → t < z → Δ n t < 0) ∧ (∀ t, z < t → 0 < Δ n t) ∧
      StrictMonoOn (Δ n) (Set.Ici z) ∧ sInf {t : ℝ | 0 < t ∧ Δ n t = 0} = z := by
  have hFD : ∀ t, 0 ≤ t → Δ n t = FD a la b lb n t := by
    intro t ht
    rw [hΔ, expMin_of_nonneg n _ (by have := hla.le; positivity),
      expMin_of_nonneg n _ (by have := (hla.trans hll).le; positivity)]
    rfl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨z, hz, hz0, hneg, hpos, hmono⟩ := FD_struct a la b lb ha hb hla hll hab hr k
  have hneg' : ∀ t, 0 < t → t < z → Δ (k + 1) t < 0 := fun t ht htz => by
    rw [hFD t ht.le]; exact hneg t ht htz
  have hpos' : ∀ t, z < t → 0 < Δ (k + 1) t := fun t htz => by
    rw [hFD t (hz.trans htz).le]; exact hpos t htz
  have hz0' : Δ (k + 1) z = 0 := by rw [hFD z hz.le]; exact hz0
  refine ⟨z, hz, hz0', hneg', hpos', ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : z ≤ x := hx
    rw [hFD x (hz.trans_le hx').le, hFD y (hz.trans_le (hx'.trans hxy.le)).le]
    exact hmono hx hy hxy
  · have : {t : ℝ | 0 < t ∧ Δ (k + 1) t = 0} = {z} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ht, h0⟩
        rcases lt_trichotomy t z with h | h | h
        · have := hneg' t ht h; linarith
        · exact h
        · have := hpos' t h; linarith
      · rintro rfl; exact ⟨hz, hz0'⟩
    rw [this, csInf_singleton]

theorem lemma3_core (a la b lb : ℝ) (hb : 0 < b) (hla : 0 < la) (hab : b < a) (hll : la < lb)
    (hr : a * la < b * lb) (Δ : ℕ → ℝ → ℝ)
    (hΔ : ∀ n t, Δ n t = a * expMinPoisson n (la * t) - b * expMinPoisson n (lb * t)) :
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < sInf {t : ℝ | 0 < t ∧ Δ n t = 0} → Δ n t < 0) ∧
    (∀ n, 1 ≤ n → ∀ t, sInf {t : ℝ | 0 < t ∧ Δ n t = 0} < t → 0 < Δ n t) ∧
    StrictMonoOn (fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}) (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → MonotoneOn (Δ n) (Set.Ioi (sInf {t : ℝ | 0 < t ∧ Δ n t = 0}))) ∧
    (∀ n, 1 ≤ n → Filter.Tendsto (Δ n) Filter.atTop (nhds ((a - b) * n))) := by
  have ha : 0 < a := hb.trans hab
  have hlb : 0 < lb := hla.trans hll
  have key := Delta_key a la b lb ha hb hla hll hab hr Δ hΔ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have : Δ n = fun t => a * Eg n (max (la * t) 0) - b * Eg n (max (lb * t) 0) := by
      funext t; rw [hΔ, expMin_eq, expMin_eq]
    rw [this]
    exact (continuous_const.mul ((Eg_cont n).comp ((continuous_const.mul continuous_id).max continuous_const))).sub
      (continuous_const.mul ((Eg_cont n).comp ((continuous_const.mul continuous_id).max continuous_const)))
  · intro n hn
    obtain ⟨z, hz, hz0, -⟩ := key n hn
    exact ⟨z, hz, hz0⟩
  · intro n hn t ht htz
    obtain ⟨z, hz, hz0, hneg, hpos, hmono, hsInf⟩ := key n hn
    rw [hsInf] at htz
    exact hneg t ht htz
  · intro n hn t htz
    obtain ⟨z, hz, hz0, hneg, hpos, hmono, hsInf⟩ := key n hn
    rw [hsInf] at htz
    exact hpos t htz
  · have step : ∀ n : ℕ, 1 ≤ n → sInf {t : ℝ | 0 < t ∧ Δ n t = 0} < sInf {t : ℝ | 0 < t ∧ Δ (n + 1) t = 0} := by
      intro n hn
      obtain ⟨z, hz, hz0, hneg, hpos, hmono, hsInf⟩ := key n hn
      obtain ⟨z', hz', hz0', hneg', hpos', hmono', hsInf'⟩ := key (n + 1) (by omega)
      rw [hsInf, hsInf']
      by_contra hcon
      push_neg at hcon
      -- Δ n z' ≤ 0
      have hle : Δ n z' ≤ 0 := by
        rcases hcon.eq_or_lt with h | h
        · rw [h]; exact hz0.le
        · exact (hneg z' hz' h).le
      have hFD : ∀ m, ∀ t, 0 ≤ t → Δ m t = FD a la b lb m t := by
        intro m t ht
        rw [hΔ, expMin_of_nonneg m _ (by have := hla.le; positivity),
          expMin_of_nonneg m _ (by have := hlb.le; positivity)]
        rfl
      have hx : 0 < la * z' := by positivity
      have hxy : la * z' < lb * z' := by nlinarith
      have hle' : a * Eg n (la * z') ≤ b * Eg n (lb * z') := by
        have := hFD n z' hz'.le
        unfold FD at this
        linarith
      have hlt := Tl_next_lt n hn a b (la * z') (lb * z') ha hb hx hxy hle'
      have h2 : Δ (n + 1) z' = Δ n z' + (a * Tl (n + 1) (la * z') - b * Tl (n + 1) (lb * z')) := by
        rw [hFD (n + 1) z' hz'.le, hFD n z' hz'.le]
        unfold FD
        rw [Eg_succ, Eg_succ]
        ring
      linarith
    intro m hm n hn hmn
    simp only [Set.mem_Ici] at hm hn
    induction n, hn using Nat.le_induction with
    | base => omega
    | succ n hn ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
      · exact (ih h).trans (step n hn)
      · subst h; exact step m hm
  · intro n hn
    obtain ⟨z, hz, hz0, hneg, hpos, hmono, hsInf⟩ := key n hn
    rw [hsInf]
    intro x hx y hy hxy
    have hx' : z < x := hx
    exact hmono.monotoneOn (Set.mem_Ici.2 hx'.le) (Set.mem_Ici.2 (hx'.trans_le hxy).le) hxy
  · intro n hn
    have hlim := FD_tendsto a la b lb n hla hlb
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hΔ, expMin_of_nonneg n _ (by have := hla.le; positivity),
      expMin_of_nonneg n _ (by have := hlb.le; positivity)]
    rfl


theorem lemma3_markdown_core (a la b lb : ℝ) (hpair : IsMarkdownPair a la b lb) :
    let Δ : ℕ → ℝ → ℝ := fun n t => PriceSwitch.Markdown.switchRevenue a la b lb n t t - PriceSwitch.Markdown.switchRevenue a la b lb n t 0
    let tn : ℕ → ℝ := fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < tn n → Δ n t < 0) ∧
    (∀ n, 1 ≤ n → ∀ t, tn n < t → 0 < Δ n t) ∧
    StrictMonoOn tn (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → MonotoneOn (Δ n) (Set.Ioi (tn n))) ∧
    (∀ n, 1 ≤ n → Tendsto (Δ n) atTop (𝓝 ((a - b) * n))) := by
  intro Δ tn
  exact lemma3_core a la b lb hpair.pos_price hpair.pos_rate hpair.price_lt hpair.rate_lt
    hpair.revRate_lt Δ (fun n t => Delta_eq a la b lb n t)

theorem lemma3_markup_core (a la b lb : ℝ) (hpair : IsMarkupPair a la b lb) :
    let Δ : ℕ → ℝ → ℝ := fun n t => PriceSwitch.Markdown.switchRevenue a la b lb n t t - PriceSwitch.Markdown.switchRevenue a la b lb n t 0
    let tn : ℕ → ℝ := fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < tn n → 0 < Δ n t) ∧
    (∀ n, 1 ≤ n → ∀ t, tn n < t → Δ n t < 0) ∧
    StrictMonoOn tn (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → AntitoneOn (Δ n) (Set.Ioi (tn n))) ∧
    (∀ n, 1 ≤ n → Tendsto (Δ n) atTop (𝓝 ((a - b) * n))) := by
  intro Δ tn
  have hΔ : ∀ n t, -Δ n t = b * expMinPoisson n (lb * t) - a * expMinPoisson n (la * t) := by
    intro n t
    have := Delta_eq a la b lb n t
    simp only [Δ]
    linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := lemma3_core b lb a la hpair.pos_price hpair.pos_rate
    hpair.price_lt hpair.rate_lt hpair.revRate_lt (fun n t => -Δ n t) hΔ
  simp only [neg_eq_zero] at h2 h3 h4 h5 h6
  refine ⟨?_, h2, ?_, ?_, h5, ?_, ?_⟩
  · intro n hn
    have h := (h1 n hn).neg
    convert h using 1
    funext t
    simp
  · intro n hn t ht htz
    have := h3 n hn t ht htz
    linarith
  · intro n hn t htz
    have := h4 n hn t htz
    linarith
  · intro n hn x hx y hy hxy
    have := h6 n hn hx hy hxy
    simp only at this
    linarith
  · intro n hn
    have := (h7 n hn).neg
    have e : -((b - a) * (n : ℝ)) = (a - b) * n := by ring
    rw [e] at this
    simpa using this

end DP3L3

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations PriceSwitch.Markdown

namespace DP872

local instance instExp1 : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure one_pos

section General

variable {Ω : Type*} [MeasurableSpace Ω] (T : ℕ → Ω → ℝ)

lemma measurableSet_mem_arr (hT : ∀ i, Measurable (T i)) (u : ℝ) (n : ℕ) :
    MeasurableSet {ω | 1 ≤ n ∧ arrivalTime T n ω ≤ u} := by
  have hm : Measurable fun ω => arrivalTime T n ω := by
    unfold arrivalTime
    exact Finset.measurable_sum _ fun i _ => hT i
  exact (MeasurableSet.const (1 ≤ n)).inter (measurableSet_le hm measurable_const)

lemma measurable_countingProcess (hT : ∀ i, Measurable (T i)) (u : ℝ) :
    Measurable (countingProcess T u) := by
  refine measurable_to_countable' fun k => ?_
  have hmem := measurableSet_mem_arr T hT u
  have hinf : MeasurableSet {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Infinite} := by
    have : {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Infinite} =
        ⋂ M : ℕ, ⋃ n : ℕ, {ω : Ω | M ≤ n} ∩ {ω | 1 ≤ n ∧ arrivalTime T n ω ≤ u} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h M
        obtain ⟨n, hn, hMn⟩ := h.exists_gt M
        exact ⟨n, hMn.le, hn⟩
      · intro h
        refine Set.infinite_of_not_bddAbove ?_
        rintro ⟨B, hB⟩
        obtain ⟨n, hBn, hn⟩ := h (B + 1)
        have := hB hn
        omega
    rw [this]
    exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
      (MeasurableSet.const _).inter (hmem n)
  have hfin : ∀ F : Finset ℕ,
      MeasurableSet {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u} = ↑F} := by
    intro F
    have : {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u} = ↑F} =
        ⋂ n : ℕ, {ω | (1 ≤ n ∧ arrivalTime T n ω ≤ u) ↔ n ∈ F} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.ext_iff, Finset.mem_coe]
    rw [this]
    refine MeasurableSet.iInter fun n => ?_
    by_cases h : n ∈ F
    · simp only [h, iff_true]
      exact hmem n
    · simp only [h, iff_false]
      exact (hmem n).compl
  have : countingProcess T u ⁻¹' {k} =
      (⋃ (F : Finset ℕ) (_ : F.card = k),
        {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u} = (F : Set ℕ)}) ∪
        ({ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Infinite} ∩ {_ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, countingProcess, Set.mem_union,
      Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases hf : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Finite
      · left
        refine ⟨hf.toFinset, ?_, hf.coe_toFinset.symm⟩
        rw [← h, Set.ncard_eq_toFinset_card _ hf]
      · right
        exact ⟨hf, by rw [← h, Set.Infinite.ncard hf]⟩
    · rintro (⟨F, hF, hA⟩ | ⟨hinf, rfl⟩)
      · rw [hA, Set.ncard_coe_finset, hF]
      · exact Set.Infinite.ncard hinf
  rw [this]
  exact (MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => hfin F).union (hinf.inter (MeasurableSet.const _))

lemma history_le (hT : ∀ i, Measurable (T i)) (s : ℝ) :
    history T s ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun u _ => (measurable_countingProcess T hT u).comap_le

/-- Sets determined by the counting process at countably many times in `[0, s]`. -/
def detSpace (s : ℝ) : MeasurableSpace Ω where
  MeasurableSet' E := ∃ D : Set ℝ, D.Countable ∧ D ⊆ Set.Icc 0 s ∧
    ∀ ω ω', (∀ u ∈ D, countingProcess T u ω = countingProcess T u ω') → (ω ∈ E ↔ ω' ∈ E)
  measurableSet_empty := ⟨∅, Set.countable_empty, Set.empty_subset _, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl E := by
    rintro ⟨D, hD, hDs, h⟩
    exact ⟨D, hD, hDs, fun ω ω' hw => not_congr (h ω ω' hw)⟩
  measurableSet_iUnion f hf := by
    choose D hD hDs h using hf
    refine ⟨⋃ i, D i, Set.countable_iUnion hD, Set.iUnion_subset hDs, fun ω ω' hw => ?_⟩
    simp only [Set.mem_iUnion]
    exact exists_congr fun i => h i ω ω' fun u hu => hw u (Set.mem_iUnion.2 ⟨i, hu⟩)

lemma history_det (s : ℝ) {E : Set Ω} (hE : MeasurableSet[history T s] E) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ Set.Icc 0 s ∧
      ∀ ω ω', (∀ u ∈ D, countingProcess T u ω = countingProcess T u ω') → (ω ∈ E ↔ ω' ∈ E) := by
  have hle : history T s ≤ detSpace T s := by
    refine iSup₂_le fun u hu => ?_
    intro E hE
    obtain ⟨C, -, rfl⟩ := hE
    exact ⟨{u}, Set.countable_singleton u, Set.singleton_subset_iff.2 hu,
      fun ω ω' h => by simp only [Set.mem_preimage, h u rfl]⟩
  exact hle E hE

end General

/-! ## The canonical model -/

abbrev Ω0 := ℕ → ℝ

def T0 : ℕ → Ω0 → ℝ := fun i ω => ω i

lemma T0_meas (i : ℕ) : Measurable (T0 i) := measurable_pi_apply i

lemma arr_succ (ω : Ω0) (n : ℕ) : arrivalTime T0 (n + 1) ω = arrivalTime T0 n ω + ω n := by
  simp [arrivalTime, T0, Finset.sum_range_succ]

lemma arr_one (ω : Ω0) : arrivalTime T0 1 ω = ω 0 := by simp [arrivalTime, T0]

lemma arr_two (ω : Ω0) : arrivalTime T0 2 ω = ω 0 + ω 1 := by
  simp [arrivalTime, T0, Finset.sum_range_succ]

lemma arr_three (ω : Ω0) : arrivalTime T0 3 ω = ω 0 + ω 1 + ω 2 := by
  simp [arrivalTime, T0, Finset.sum_range_succ]

lemma arr_mono {ω : Ω0} (hω : ∀ i, 0 < ω i) : StrictMono fun n => arrivalTime T0 n ω :=
  strictMono_nat_of_lt_succ fun n => by rw [arr_succ]; linarith [hω n]

lemma cnt_zero {ω : Ω0} {u : ℝ} (h : ∀ n, 1 ≤ n → u < arrivalTime T0 n ω) :
    countingProcess T0 u ω = 0 := by
  have : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    exact h n
  simp [countingProcess, this]

lemma cnt_one {ω : Ω0} {u : ℝ} (h1 : arrivalTime T0 1 ω ≤ u)
    (h : ∀ n, 2 ≤ n → u < arrivalTime T0 n ω) : countingProcess T0 u ω = 1 := by
  have : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} = {1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn1, hn⟩
      by_contra hne
      have := h n (by omega)
      linarith
    · rintro rfl
      exact ⟨le_rfl, h1⟩
  simp [countingProcess, this]

lemma cnt_two {ω : Ω0} {u : ℝ} (h1 : arrivalTime T0 1 ω ≤ u) (h2 : arrivalTime T0 2 ω ≤ u)
    (h : ∀ n, 3 ≤ n → u < arrivalTime T0 n ω) : countingProcess T0 u ω = 2 := by
  have : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} = {1, 2} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn1, hn⟩
      by_contra hne
      push_neg at hne
      have := h n (by omega)
      linarith
    · rintro (rfl | rfl)
      · exact ⟨le_rfl, h1⟩
      · exact ⟨by norm_num, h2⟩
  rw [countingProcess, this, Set.ncard_pair (by norm_num)]

lemma cnt_ne_one {ω : Ω0} (hω : ∀ i, 0 < ω i) {u : ℝ} (h2 : arrivalTime T0 2 ω ≤ u) :
    countingProcess T0 u ω ≠ 1 := by
  have h1 : arrivalTime T0 1 ω ≤ u :=
    le_trans ((arr_mono hω).monotone (by norm_num : 1 ≤ 2)) h2
  show {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u}.ncard ≠ 1
  by_cases hf : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u}.Finite
  · have hsub : ({1, 2} : Set ℕ) ⊆ {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} := by
      intro n hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl
      · exact ⟨le_rfl, h1⟩
      · exact ⟨by norm_num, h2⟩
    have := Set.ncard_le_ncard hsub hf
    rw [Set.ncard_pair (by norm_num)] at this
    omega
  · rw [Set.Infinite.ncard hf]
    norm_num

lemma cnt_lt2 {ω : Ω0} (hω : ∀ i, 0 < ω i) {u : ℝ} (hu : u < arrivalTime T0 2 ω) :
    countingProcess T0 u ω = if ω 0 ≤ u then 1 else 0 := by
  have hge : ∀ n, 2 ≤ n → u < arrivalTime T0 n ω := fun n hn =>
    lt_of_lt_of_le hu ((arr_mono hω).monotone hn)
  split_ifs with h
  · exact cnt_one (by rw [arr_one]; exact h) hge
  · refine cnt_zero fun n hn => ?_
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [arr_one]
      exact not_le.1 h
    · exact hge n hn2

lemma cnt_good {ω : Ω0} (hω : ∀ i, 0 < ω i) {u : ℝ} (hu : u < ω 0 + ω 1) :
    countingProcess T0 u ω = if ω 0 ≤ u then 1 else 0 :=
  cnt_lt2 hω (by rw [arr_two]; exact hu)

/-- A good path with first arrival at `s` and no second arrival before `s + 2`. -/
noncomputable def ws (s : ℝ) : Ω0 := fun i => if i = 0 then s else 2

lemma ws_pos {s : ℝ} (hs : 0 < s) : ∀ i, 0 < ws s i := fun i => by
  unfold ws
  split_ifs <;> linarith

lemma cnt_ws {s u : ℝ} (hs : 0 < s) (hu : u < s + 2) :
    countingProcess T0 u (ws s) = if s ≤ u then 1 else 0 := by
  have h := cnt_lt2 (ws_pos hs) (u := u) (by rw [arr_two]; simp [ws]; linarith)
  simpa [ws] using h

lemma measurable_ws : Measurable ws := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i = 0
  · simp only [ws, hi, if_true]
    exact measurable_id
  · simp only [ws, hi, if_false]
    exact measurable_const

/-- A bad path: one arrival at `s`, then arrivals decreasing to `s` from above, so the counting
process is `1` at `s` and `0` everywhere else. -/
noncomputable def sp (s : ℝ) : Ω0 := fun i =>
  if i = 0 then s else if i = 1 then 1 else 1 / (i : ℝ) - 1 / ((i : ℝ) - 1)

lemma sp_arr (s : ℝ) (j : ℕ) : arrivalTime T0 (j + 2) (sp s) = s + 1 / ((j : ℝ) + 1) := by
  induction j with
  | zero => simp [arrivalTime, T0, sp, Finset.sum_range_succ]
  | succ j ih =>
    rw [show j + 1 + 2 = (j + 2) + 1 by ring, arr_succ, ih]
    simp only [sp, show j + 2 ≠ 0 by omega, show j + 2 ≠ 1 by omega, if_false]
    push_cast
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (j : ℝ) + 2 - 1 = (j : ℝ) + 1 := by ring
    rw [h3]
    field_simp
    ring

lemma cnt_sp {s u : ℝ} : countingProcess T0 u (sp s) = if u = s then 1 else 0 := by
  have h1 : arrivalTime T0 1 (sp s) = s := by rw [arr_one]; simp [sp]
  have hgt : ∀ n, 2 ≤ n → s < arrivalTime T0 n (sp s) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    rw [sp_arr]
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  rcases lt_trichotomy u s with h | h | h
  · rw [if_neg h.ne]
    refine cnt_zero fun n hn => ?_
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [h1]
      exact h
    · exact h.trans (hgt n hn2)
  · subst h
    rw [if_pos rfl]
    exact cnt_one h1.le hgt
  · rw [if_neg h.ne']
    have hinf : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n (sp s) ≤ u}.Infinite := by
      obtain ⟨J, hJ⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      refine Set.infinite_of_forall_exists_gt fun M => ⟨M + J + 2, ⟨by omega, ?_⟩, by omega⟩
      rw [sp_arr]
      have : 1 / (((M + J : ℕ) : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      linarith
    exact Set.Infinite.ncard hinf


/-! ## The measure -/

section Measure

noncomputable def P0 : Measure Ω0 := Measure.infinitePi fun _ : ℕ => expMeasure (1 : ℝ)

lemma P0_prob : IsProbabilityMeasure P0 := by
  unfold P0
  infer_instance

lemma hT0 : IsExpInterarrivals P0 1 T0 where
  measurable := T0_meas
  indep := iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure (1 : ℝ))
    (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  law i := Measure.infinitePi_map_eval _ i

lemma mu_Iic_zero : expMeasure (1 : ℝ) (Set.Iic 0) = 0 := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos, if_pos le_rfl]
  simp

lemma mu_Iic (c : ℝ) (hc : 0 ≤ c) :
    expMeasure (1 : ℝ) (Set.Iic c) = ENNReal.ofReal (1 - Real.exp (-c)) := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos, if_pos hc, one_mul]

lemma mu_Ioc {c : ℝ} (hc : 0 < c) : expMeasure (1 : ℝ) (Set.Ioc 0 c) ≠ 0 := by
  intro h
  have hsub : Set.Iic c ⊆ Set.Ioc 0 c ∪ Set.Iic 0 := by
    intro x hx
    rcases le_or_gt x 0 with h' | h'
    · exact Or.inr h'
    · exact Or.inl ⟨h', hx⟩
  have := measure_mono_null hsub (measure_union_null h mu_Iic_zero)
  rw [mu_Iic c hc.le, ENNReal.ofReal_eq_zero] at this
  have : Real.exp (-c) < 1 := by
    have h := Real.exp_lt_exp.2 (show -c < 0 by linarith)
    rwa [Real.exp_zero] at h
  linarith

lemma mu_Ioi_one : expMeasure (1 : ℝ) (Set.Ioi 1) ≠ 0 := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, mu_Iic 1 zero_le_one]
  intro h
  have h1 : ENNReal.ofReal (1 - Real.exp (-1)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    have := Real.exp_pos (-1)
    linarith
  exact (tsub_pos_of_lt h1).ne' h

lemma mu_countable {D : Set ℝ} (hD : D.Countable) : expMeasure (1 : ℝ) D = 0 := by
  change (volume.withDensity (gammaPDF 1 1)) D = 0
  exact withDensity_absolutelyContinuous _ _ (hD.measure_zero volume)

lemma good_ae : ∀ᵐ ω ∂P0, ∀ i, 0 < ω i := by
  refine ae_all_iff.2 fun i => ?_
  rw [ae_iff]
  have : {ω : Ω0 | ¬ 0 < ω i} = T0 i ⁻¹' Set.Iic 0 := by
    ext ω
    simp [T0]
  rw [this, ← Measure.map_apply (T0_meas i) measurableSet_Iic, hT0.law i]
  exact mu_Iic_zero

lemma pair : IsMarkdownPair 2 1 1 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Measure

/-! ## Every admissible switching time sells nothing before switching -/

section Main

variable {τ : Ω0 → ℝ} (hτ : IsAdmissible P0 T0 1 1 τ)
include hτ

lemma tau_meas : Measurable τ :=
  measurable_of_Iic fun v => history_le T0 T0_meas v _ (hτ.stopping v)

lemma pathdet (v : ℝ) (ω ω' : Ω0)
    (h : ∀ u ∈ Set.Icc (0 : ℝ) v, countingProcess T0 u ω = countingProcess T0 u ω') :
    τ ω ≤ v ↔ τ ω' ≤ v := by
  obtain ⟨D, -, hDs, hD⟩ := history_det T0 v (hτ.stopping v)
  exact hD ω ω' fun u hu => h u (hDs hu)

lemma K1 {ω : Ω0} (hω : ∀ i, 0 < ω i) (hlt : τ ω < ω 0 + ω 1) : τ ω = τ (ws (ω 0)) := by
  have hagree : ∀ v, v < ω 0 + ω 1 → v ≤ 1 → (τ ω ≤ v ↔ τ (ws (ω 0)) ≤ v) := by
    intro v hv hv1
    refine pathdet hτ v _ _ fun u hu => ?_
    rw [cnt_good hω (lt_of_le_of_lt hu.2 hv), cnt_ws (hω 0) (by linarith [hu.2, hω 0])]
  have h1 := hτ.le_horizon ω
  have h2 := hτ.le_horizon (ws (ω 0))
  rcases lt_trichotomy (τ ω) (τ (ws (ω 0))) with h | h | h
  · exact absurd ((hagree _ hlt h1).1 le_rfl) (not_le.2 h)
  · exact h
  · exact absurd ((hagree _ (h.trans hlt) h2).2 le_rfl) (not_le.2 h)

lemma K2 {ω : Ω0} (hω : ∀ i, 0 < ω i) (hρ : ω 0 + ω 1 ≤ τ (ws (ω 0))) : ω 0 + ω 1 ≤ τ ω := by
  by_contra h
  rw [not_le] at h
  have := K1 hτ hω h
  linarith

lemma K3 {s v s'' : ℝ} (hs : 0 < s) (hQ : τ (ws s) = s) (hsv : s < v) (D : Set ℝ)
    (hDs : D ⊆ Set.Icc 0 v)
    (hD : ∀ ω ω', (∀ u ∈ D, countingProcess T0 u ω = countingProcess T0 u ω') →
      (ω ∈ {ω | τ ω ≤ v} ↔ ω' ∈ {ω | τ ω ≤ v}))
    (hsD : s ∉ D) (hv : v < s'') : τ (ws s'') ≤ v := by
  have hsp : τ (sp s) ≤ s := by
    refine (pathdet hτ s (ws s) (sp s) fun u hu => ?_).1 hQ.le
    rw [cnt_ws hs (by linarith [hu.2]), cnt_sp]
    by_cases hus : u = s
    · simp [hus]
    · have : ¬ s ≤ u := fun h => hus (le_antisymm hu.2 h)
      simp [hus, this]
  have hu' : ∀ u ∈ D, countingProcess T0 u (sp s) = countingProcess T0 u (ws s'') := by
    intro u hu
    have hu2 := hDs hu
    have hne : u ≠ s := fun h => hsD (h ▸ hu)
    rw [cnt_sp, cnt_ws (hs.trans (hsv.trans hv)) (by linarith [hu2.2]), if_neg hne,
      if_neg (not_le.2 (lt_of_le_of_lt hu2.2 hv))]
  exact (hD (sp s) (ws s'') hu').1 (hsp.trans hsv.le)

lemma mu_Q : expMeasure (1 : ℝ) {s | 0 < s ∧ τ (ws s) = s} = 0 := by
  set μ := expMeasure (1 : ℝ) with hμ
  set Q := {s : ℝ | 0 < s ∧ τ (ws s) = s} with hQdef
  by_contra hQ0
  set S := {v : ℝ | 0 < μ (Q ∩ Set.Iio v)} with hSdef
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hQ0
    have : Q = ⋃ m : ℕ, Q ∩ Set.Iio (m : ℝ) := by
      ext s
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iio]
      exact ⟨fun h => let ⟨m, hm⟩ := exists_nat_gt s; ⟨m, h, hm⟩, fun ⟨_, h, _⟩ => h⟩
    rw [this]
    refine measure_iUnion_null fun m => ?_
    have : (m : ℝ) ∉ S := by rw [hne]; exact Set.notMem_empty _
    simpa [S, pos_iff_ne_zero] using this
  have hSbdd : BddBelow S := ⟨0, fun v hv => by
    by_contra h
    rw [not_le] at h
    have : Q ∩ Set.Iio v = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs hsv
      have := hs.1
      linarith
    have hv' : 0 < μ (Q ∩ Set.Iio v) := hv
    rw [this, measure_empty] at hv'
    exact lt_irrefl _ hv'⟩
  set q0 := sInf S with hq0
  have hbelow : ∀ v < q0, μ (Q ∩ Set.Iio v) = 0 := fun v hv => by
    have := notMem_of_lt_csInf hv hSbdd
    simpa [S, pos_iff_ne_zero] using this
  have hIio : μ (Q ∩ Set.Iio q0) = 0 := by
    have : Q ∩ Set.Iio q0 = ⋃ k : ℕ, Q ∩ Set.Iio (q0 - 1 / ((k : ℝ) + 1)) := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_iUnion]
      constructor
      · rintro ⟨hs, hsq⟩
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hsq)
        exact ⟨k, hs, by linarith⟩
      · rintro ⟨k, hs, hsk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact ⟨hs, by linarith⟩
    rw [this]
    exact measure_iUnion_null fun k => hbelow _
      (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith)
  have hIic : μ (Q ∩ Set.Iic q0) = 0 := by
    refine measure_mono_null (t := (Q ∩ Set.Iio q0) ∪ {q0}) ?_
      (measure_union_null hIio (mu_countable (Set.countable_singleton _)))
    rintro s ⟨hs, hsq⟩
    rcases (Set.mem_Iic.1 hsq).lt_or_eq with h | h
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr h
  have hIoi : μ (Q ∩ Set.Ioi q0) ≠ 0 := by
    intro h
    apply hQ0
    refine measure_mono_null (t := (Q ∩ Set.Iic q0) ∪ (Q ∩ Set.Ioi q0)) ?_
      (measure_union_null hIic h)
    intro s hs
    rcases le_or_gt s q0 with h' | h'
    · exact Or.inl ⟨hs, h'⟩
    · exact Or.inr ⟨hs, h'⟩
  obtain ⟨s'', hs''Q, hs''q⟩ := nonempty_of_measure_ne_zero hIoi
  rw [Set.mem_Ioi] at hs''q
  have hq0v : q0 < (q0 + s'') / 2 := by linarith
  have hvs'' : (q0 + s'') / 2 < s'' := by linarith
  set v := (q0 + s'') / 2 with hv
  obtain ⟨e, heS, hev⟩ := exists_lt_of_csInf_lt hSne hq0v
  have hv_pos : μ (Q ∩ Set.Iio v) ≠ 0 :=
    (lt_of_lt_of_le heS (measure_mono (Set.inter_subset_inter_right _
      (Set.Iio_subset_Iio hev.le)))).ne'
  obtain ⟨D, hDc, hDs, hD⟩ := history_det T0 v (hτ.stopping v)
  have hdiff : μ ((Q ∩ Set.Iio v) \ D) ≠ 0 := by
    intro h
    apply hv_pos
    refine measure_mono_null (t := ((Q ∩ Set.Iio v) \ D) ∪ D) ?_
      (measure_union_null h (mu_countable hDc))
    intro s hs
    by_cases hsD : s ∈ D
    · exact Or.inr hsD
    · exact Or.inl ⟨hs, hsD⟩
  obtain ⟨s, ⟨hsQ, hsv⟩, hsD⟩ := nonempty_of_measure_ne_zero hdiff
  have := K3 hτ hsQ.1 hsQ.2 hsv D hDs hD hsD hvs''
  rw [hs''Q.2] at this
  linarith

lemma mu_R (k : ℕ) :
    expMeasure (1 : ℝ) {s | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} = 0 := by
  have : IsProbabilityMeasure P0 := P0_prob
  set R := {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} with hRdef
  have hρ : Measurable fun s => τ (ws s) := (tau_meas hτ).comp measurable_ws
  have hRm : MeasurableSet R :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le (measurable_id.add_const _) hρ)
  by_contra hR
  set c : ℝ := 1 / ((k : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  set t : ℕ → Set ℝ := fun i => if i = 0 then R else if i = 1 then Set.Ioc 0 c else Set.Ioi 1
    with htdef
  have hEv : P0 (Set.pi (↑({0, 1, 2} : Finset ℕ)) t) ≠ 0 := by
    have hmt : ∀ i ∈ ({0, 1, 2} : Finset ℕ), MeasurableSet (t i) := by
      intro i _
      simp only [htdef]
      split_ifs
      · exact hRm
      · exact measurableSet_Ioc
      · exact measurableSet_Ioi
    unfold P0
    rw [Measure.infinitePi_pi _ hmt]
    simp only [htdef, Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
      Finset.prod_singleton]
    norm_num
    exact ⟨hR, mu_Ioc hc, mu_Ioi_one⟩
  apply hEv
  refine measure_mono_null ?_ (measure_union_null (ae_iff.1 good_ae) (ae_iff.1 hτ.stock))
  intro ω hω
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_cases hpos : ∀ i, 0 < ω i
  swap
  · exact Or.inl hpos
  right
  have h0 : ω 0 ∈ R := by simpa [htdef] using hω 0 (by simp)
  have h1 : ω 1 ∈ Set.Ioc 0 c := by simpa [htdef] using hω 1 (by simp)
  have h2 : ω 2 ∈ Set.Ioi 1 := by simpa [htdef] using hω 2 (by simp)
  have hS2 : ω 0 + ω 1 ≤ τ ω := K2 hτ hpos (by linarith [h0.2, h1.2])
  have hτ1 := hτ.le_horizon ω
  have h3 : ∀ n, 3 ≤ n → τ ω < arrivalTime T0 n ω := by
    intro n hn
    have := (arr_mono hpos).monotone hn
    rw [arr_three] at this
    simp only [Set.mem_Ioi] at h2
    linarith [hpos 0, hpos 1]
  rw [cnt_two (by rw [arr_one]; linarith [hpos 1]) (by rw [arr_two]; exact hS2) h3]
  norm_num

lemma ae_cnt_zero : ∀ᵐ ω ∂P0, countingProcess T0 (τ ω) ω = 0 := by
  have : IsProbabilityMeasure P0 := P0_prob
  have hQ : ∀ᵐ ω ∂P0, ω 0 ∉ {s : ℝ | 0 < s ∧ τ (ws s) = s} := by
    rw [ae_iff]
    simp only [not_not]
    apply nonpos_iff_eq_zero.1
    calc P0 {ω | ω 0 ∈ {s : ℝ | 0 < s ∧ τ (ws s) = s}}
        = P0 (T0 0 ⁻¹' {s : ℝ | 0 < s ∧ τ (ws s) = s}) := rfl
      _ ≤ P0.map (T0 0) {s : ℝ | 0 < s ∧ τ (ws s) = s} :=
          Measure.le_map_apply (T0_meas 0).aemeasurable _
      _ = 0 := by rw [hT0.law 0]; exact mu_Q hτ
  have hR : ∀ᵐ ω ∂P0, ∀ k : ℕ, ω 0 ∉ {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} := by
    refine ae_all_iff.2 fun k => ?_
    rw [ae_iff]
    simp only [not_not]
    apply nonpos_iff_eq_zero.1
    calc P0 {ω | ω 0 ∈ {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)}}
        = P0 (T0 0 ⁻¹' {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)}) := rfl
      _ ≤ P0.map (T0 0) {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} :=
          Measure.le_map_apply (T0_meas 0).aemeasurable _
      _ = 0 := by rw [hT0.law 0]; exact mu_R hτ k
  filter_upwards [good_ae, hτ.stock, hQ, hR] with ω hpos hst hq hr
  by_contra hne
  have h1 : countingProcess T0 (τ ω) ω = 1 := by omega
  have hlt : τ ω < ω 0 + ω 1 := by
    by_contra h
    rw [not_lt] at h
    exact cnt_ne_one hpos (by rw [arr_two]; exact h) h1
  have hge : ω 0 ≤ τ ω := by
    by_contra h
    rw [not_le] at h
    rw [cnt_good hpos hlt, if_neg (not_le.2 h)] at h1
    exact zero_ne_one h1
  have heq := K1 hτ hpos hlt
  rcases hge.lt_or_eq with h | h
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    exact hr k ⟨hpos 0, by rw [← heq]; linarith⟩
  · exact hq ⟨hpos 0, heq.symm.trans h.symm⟩

end Main

end DP872



set_option autoImplicit false

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations PriceSwitch.Markdown
  PriceSwitch.UpOrDown

namespace DP3

open DP3L3 Nat

/-! ## Real-analysis helpers -/

lemma neg_pos_root (f : ℝ → ℝ) (a : ℝ) (hc : Continuous f) (hroot : ∃ t, 0 < t ∧ f t = 0)
    (hneg : ∀ t, 0 < t → t < a → f t < 0) (hpos : ∀ t, a < t → 0 < f t) :
    0 < a ∧ f a = 0 := by
  obtain ⟨t0, ht0, hft0⟩ := hroot
  have ha : 0 < a := by
    by_contra h
    push_neg at h
    have := hpos t0 (by linarith)
    linarith
  refine ⟨ha, le_antisymm ?_ ?_⟩
  · have hT : Filter.Tendsto f (nhdsWithin a (Set.Iio a)) (nhds (f a)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsLT ha] with t ht
    exact (hneg t ht.1 ht.2).le
  · have hT : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (f a)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpos t ht).le

lemma order_lemma (D1 D2 D : ℝ → ℝ) (hD : ∀ t, D t = D2 t - D1 t) (a b s0 : ℝ)
    (c1 : Continuous D1) (c2 : Continuous D2)
    (ha : 0 < a) (hDa : D1 a = 0) (hneg1 : ∀ t, 0 < t → t < a → D1 t < 0)
    (hpos1 : ∀ t, a < t → 0 < D1 t)
    (hb : 0 < b) (hDb : D2 b = 0) (hpos2 : ∀ t, 0 < t → t < b → 0 < D2 t)
    (hneg2 : ∀ t, b < t → D2 t < 0)
    (hs0 : 0 < s0) (h1 : 0 < D1 s0) (h2 : 0 < D2 s0) :
    a < sInf {t | 0 < t ∧ D t = 0} ∧ sInf {t | 0 < t ∧ D t = 0} < b := by
  have has0 : a < s0 := by
    by_contra h
    push_neg at h
    rcases h.lt_or_eq with h | h
    · linarith [hneg1 s0 hs0 h]
    · rw [h] at h1; linarith
  have hs0b : s0 < b := by
    by_contra h
    push_neg at h
    rcases h.lt_or_eq with h | h
    · linarith [hneg2 s0 h]
    · rw [← h] at h2; linarith
  have hab : a < b := has0.trans hs0b
  have cD : Continuous D := by
    have : D = fun t => D2 t - D1 t := funext hD
    rw [this]; exact c2.sub c1
  have hDa' : 0 < D a := by rw [hD, hDa]; linarith [hpos2 a ha hab]
  have hDb' : D b < 0 := by rw [hD, hDb]; linarith [hpos1 b hab]
  obtain ⟨r, hr, hDr⟩ : ∃ r ∈ Set.Ioo a b, D r = 0 :=
    intermediate_value_Ioo' hab.le cD.continuousOn ⟨hDb', hDa'⟩
  have hne : ({t | 0 < t ∧ D t = 0} : Set ℝ).Nonempty := ⟨r, ha.trans hr.1, hDr⟩
  have hbdd : BddBelow ({t | 0 < t ∧ D t = 0} : Set ℝ) := ⟨0, fun t ht => ht.1.le⟩
  refine ⟨?_, lt_of_le_of_lt (csInf_le hbdd ⟨ha.trans hr.1, hDr⟩) hr.2⟩
  have hev : ∀ᶠ t in nhds a, 0 < D t := cD.continuousAt.eventually (lt_mem_nhds hDa')
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hle : a + ε / 2 ≤ sInf {t | 0 < t ∧ D t = 0} := by
    refine le_csInf hne fun t ht => ?_
    by_contra hlt
    push_neg at hlt
    rcases le_or_gt t a with hta | hta
    · have hD1 : D1 t ≤ 0 := by
        rcases hta.lt_or_eq with h | h
        · exact (hneg1 t ht.1 h).le
        · rw [h, hDa]
      have := hpos2 t ht.1 (by linarith)
      have := ht.2
      rw [hD] at this
      linarith
    · have hdist : dist t a < ε := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have := hball hdist
      linarith [ht.2]
  linarith

/-! ## Bounds on `Eg n m = E min(n, Poisson(m))` -/

lemma FF_nonneg (n : ℕ) (m : ℝ) (hm : 0 ≤ m) : 0 ≤ FF n m := by
  unfold FF
  exact Finset.sum_nonneg fun k _ => by positivity

lemma FF_le_one (n : ℕ) (m : ℝ) (hm : 0 ≤ m) : FF n m ≤ 1 := by
  unfold FF
  have h := Real.sum_le_exp_of_nonneg hm n
  have : ∑ k ∈ Finset.range n, Real.exp (-m) * m ^ k / (k ! : ℝ)
      = Real.exp (-m) * ∑ k ∈ Finset.range n, m ^ k / (k ! : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  calc Real.exp (-m) * ∑ k ∈ Finset.range n, m ^ k / (k ! : ℝ)
      ≤ Real.exp (-m) * Real.exp m := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma FF_mono (j n : ℕ) (hjn : j ≤ n) (m : ℝ) (hm : 0 ≤ m) : FF j m ≤ FF n m := by
  unfold FF
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hjn) ?_
  intro k _ _; positivity

lemma FF_chernoff (n : ℕ) (m : ℝ) (hm : 0 ≤ m) :
    FF n m ≤ 2 ^ n * Real.exp (-(m / 2)) := by
  unfold FF
  have hterm : ∀ k ∈ Finset.range n, Real.exp (-m) * m ^ k / (k ! : ℝ)
      ≤ Real.exp (-m) * 2 ^ n * ((m / 2) ^ k / (k ! : ℝ)) := by
    intro k hk
    have hk' : k ≤ n := (Finset.mem_range.1 hk).le
    have h2 : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hk'
    have hmk : m ^ k = 2 ^ k * (m / 2) ^ k := by
      rw [← mul_pow]; ring_nf
    rw [hmk]
    have hpos : 0 ≤ (m / 2) ^ k / (k ! : ℝ) := by positivity
    have he := (Real.exp_pos (-m)).le
    calc Real.exp (-m) * (2 ^ k * (m / 2) ^ k) / (k ! : ℝ)
        = Real.exp (-m) * 2 ^ k * ((m / 2) ^ k / (k ! : ℝ)) := by ring
      _ ≤ Real.exp (-m) * 2 ^ n * ((m / 2) ^ k / (k ! : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          exact mul_le_mul_of_nonneg_left h2 he
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hs := Real.sum_le_exp_of_nonneg (show 0 ≤ m / 2 by positivity) n
  calc Real.exp (-m) * 2 ^ n * ∑ i ∈ Finset.range n, (m / 2) ^ i / (i ! : ℝ)
      ≤ Real.exp (-m) * 2 ^ n * Real.exp (m / 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 2 ^ n * Real.exp (-(m / 2)) := by
        rw [mul_comm (Real.exp (-m)), mul_assoc, ← Real.exp_add]; congr 2; ring

lemma Eg_le_n (n : ℕ) (m : ℝ) (hm : 0 ≤ m) : Eg n m ≤ n := by
  unfold Eg Tl
  calc ∑ j ∈ Finset.Icc 1 n, (1 - FF j m) ≤ ∑ _j ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => by linarith [FF_nonneg j m hm]
    _ = n := by simp

lemma Eg_ge (n : ℕ) (m : ℝ) (hm : 0 ≤ m) : (n : ℝ) * (1 - FF n m) ≤ Eg n m := by
  unfold Eg Tl
  calc (n : ℝ) * (1 - FF n m) = ∑ _j ∈ Finset.Icc 1 n, (1 - FF n m) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ ∑ j ∈ Finset.Icc 1 n, (1 - FF j m) :=
        Finset.sum_le_sum fun j hj => by
          linarith [FF_mono j n (Finset.mem_Icc.1 hj).2 m hm]

lemma Eg_le_m (n : ℕ) (m : ℝ) (hm : 0 ≤ m) : Eg n m ≤ m := by
  have hmono : MonotoneOn (fun x => x - Eg n x) (Set.Ici 0) := by
    have hd : ∀ x, HasDerivAt (fun x => x - Eg n x) (1 - FF n x) x :=
      fun x => (hasDerivAt_id x).sub (Eg_hasDerivAt n x)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_id.sub (Eg_cont n)).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      linarith [FF_le_one n x (le_of_lt hx)]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hm) hm
  simp only [Eg_zero, sub_zero] at this
  linarith

lemma exp4_ge : (20 : ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  have := pow_le_pow_left₀ (by norm_num) h27 4
  norm_num at this
  linarith

lemma Eg_8n (n : ℕ) (hn : 1 ≤ n) : (9 / 10 : ℝ) * n ≤ Eg n (8 * n) := by
  have hm : (0 : ℝ) ≤ 8 * n := by positivity
  have hc := FF_chernoff n (8 * n) hm
  have hq : (2 : ℝ) ^ n * Real.exp (-(8 * (n : ℝ) / 2)) = (2 * Real.exp (-4)) ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have hq0 : 0 ≤ 2 * Real.exp (-4) := by positivity
  have hq1 : 2 * Real.exp (-4) ≤ 1 / 10 := by
    rw [Real.exp_neg]
    have := exp4_ge
    rw [mul_inv_le_iff₀ (Real.exp_pos 4)]
    linarith
  have hpow : (2 * Real.exp (-4)) ^ n ≤ 2 * Real.exp (-4) :=
    pow_le_of_le_one hq0 (by linarith) (by omega)
  have hFF : FF n (8 * n) ≤ 1 / 10 := by linarith
  have := Eg_ge n (8 * n) hm
  have hn' : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-! ## The parameters `p₁ = 3/4, λ₁ = 4, p = 1, λ = 1, p₂ = 2, λ₂ = 1/20` -/

lemma three : IsThreePrice (3 / 4) 4 1 1 2 (1 / 20) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

lemma mdpair : IsMarkdownPair 1 1 (3 / 4) 4 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma mupair : IsMarkupPair 1 1 2 (1 / 20) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma d1_eq (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    delta1 (3 / 4) 4 1 1 2 (1 / 20) n t = Eg n t - 3 / 4 * Eg n (4 * t) := by
  unfold delta1
  rw [Delta_eq, expMin_of_nonneg _ _ (by linarith), expMin_of_nonneg _ _ (by linarith)]
  ring

lemma d2_eq (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    delta2 (3 / 4) 4 1 1 2 (1 / 20) n t = Eg n t - 2 * Eg n (1 / 20 * t) := by
  unfold delta2
  rw [Delta_eq, expMin_of_nonneg _ _ (by linarith), expMin_of_nonneg _ _ (by positivity)]
  ring

lemma sw_tt (a la b lb : ℝ) (n : ℕ) (t : ℝ) :
    switchRevenue a la b lb n t t = a * expMinPoisson n (la * t) := by
  unfold switchRevenue
  simp only [sub_self, mul_zero, add_zero]
  ring

lemma d_eq (n : ℕ) (t : ℝ) :
    delta (3 / 4) 4 1 1 2 (1 / 20) n t =
      delta2 (3 / 4) 4 1 1 2 (1 / 20) n t - delta1 (3 / 4) 4 1 1 2 (1 / 20) n t := by
  unfold delta delta1 delta2
  rw [sw_tt, sw_tt]; ring

lemma hassume_holds : ∀ n : ℕ, 1 ≤ n →
    tThr1 (3 / 4) 4 1 1 2 (1 / 20) n < tThr (3 / 4) 4 1 1 2 (1 / 20) n ∧
    tThr (3 / 4) 4 1 1 2 (1 / 20) n < tThr2 (3 / 4) 4 1 1 2 (1 / 20) n := by
  intro n hn
  obtain ⟨c1, r1, n1, p1, -, -, -⟩ := lemma3_markdown_core 1 1 (3 / 4) 4 mdpair
  obtain ⟨c2, r2, p2, n2, -, -, -⟩ := lemma3_markup_core 1 1 2 (1 / 20) mupair
  have hc1 : Continuous (delta1 (3 / 4) 4 1 1 2 (1 / 20) n) := c1 n hn
  have hc2 : Continuous (delta2 (3 / 4) 4 1 1 2 (1 / 20) n) := c2 n hn
  obtain ⟨ha, hDa⟩ := neg_pos_root (delta1 (3 / 4) 4 1 1 2 (1 / 20) n)
    (tThr1 (3 / 4) 4 1 1 2 (1 / 20) n) hc1 (r1 n hn) (n1 n hn) (p1 n hn)
  obtain ⟨hb, hDb⟩ := neg_pos_root (fun t => -delta2 (3 / 4) 4 1 1 2 (1 / 20) n t)
    (tThr2 (3 / 4) 4 1 1 2 (1 / 20) n) hc2.neg
    (by obtain ⟨t, ht, h⟩ := r2 n hn; exact ⟨t, ht, by simp only at h ⊢; unfold delta2; linarith⟩)
    (fun t ht hlt => by have := p2 n hn t ht hlt; simp only at this ⊢; unfold delta2; linarith)
    (fun t hlt => by have := n2 n hn t hlt; simp only at this ⊢; unfold delta2; linarith)
  have hs0 : (0 : ℝ) < 8 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hE := Eg_8n n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < delta1 (3 / 4) 4 1 1 2 (1 / 20) n (8 * n) := by
    rw [d1_eq n _ hs0.le]
    have := Eg_le_n n (4 * (8 * n)) (by positivity)
    linarith
  have h2 : 0 < delta2 (3 / 4) 4 1 1 2 (1 / 20) n (8 * n) := by
    rw [d2_eq n _ hs0.le]
    have := Eg_le_m n (1 / 20 * (8 * n)) (by positivity)
    linarith
  exact order_lemma _ _ _ (d_eq n) _ _ (8 * n) hc1 hc2 ha hDa (n1 n hn) (p1 n hn) hb
    (by simpa using hDb) (fun t ht hlt => by
      have := p2 n hn t ht hlt; simp only at this; unfold delta2; linarith)
    (fun t hlt => by have := n2 n hn t hlt; simp only at this; unfold delta2; linarith)
    hs0 h1 h2

lemma tThr1_one_gt : 1 < tThr1 (3 / 4) 4 1 1 2 (1 / 20) 1 := by
  obtain ⟨c1, r1, n1, p1, -, -, -⟩ := lemma3_markdown_core 1 1 (3 / 4) 4 mdpair
  obtain ⟨ha, hDa⟩ := neg_pos_root (delta1 (3 / 4) 4 1 1 2 (1 / 20) 1)
    (tThr1 (3 / 4) 4 1 1 2 (1 / 20) 1) (c1 1 le_rfl) (r1 1 le_rfl) (n1 1 le_rfl) (p1 1 le_rfl)
  have hval : delta1 (3 / 4) 4 1 1 2 (1 / 20) 1 1 < 0 := by
    rw [d1_eq 1 1 zero_le_one]
    simp [Eg, Tl, FF]
    have h1 := Real.exp_one_lt_d9
    have h4 := exp4_ge
    have he1 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have he4 : Real.exp (-4) = (Real.exp 4)⁻¹ := Real.exp_neg 4
    have hp1 := Real.exp_pos 1
    have hp4 := Real.exp_pos 4
    have hi1 : (1 : ℝ) / 2.7182818286 < (Real.exp 1)⁻¹ := by
      rw [one_div]; exact inv_strictAnti₀ hp1 h1
    have hi4 : (Real.exp 4)⁻¹ ≤ 1 / 20 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h4
    rw [he1, he4]
    norm_num at hi1 hi4 ⊢
    linarith
  by_contra h
  push_neg at h
  rcases h.lt_or_eq with h | h
  · have : 0 < delta1 (3 / 4) 4 1 1 2 (1 / 20) 1 1 := p1 1 le_rfl 1 h
    linarith
  · rw [h] at hDa; linarith

end DP3


set_option autoImplicit false

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations PriceSwitch.Markdown
  PriceSwitch.UpOrDown

namespace DP3

open DP3L3 Nat

lemma Eg_one (m : ℝ) : Eg 1 m = 1 - Real.exp (-m) := by
  simp [Eg, Tl, FF]

lemma sw1 (b lb u : ℝ) (hu : 0 ≤ u) (hlb : 0 ≤ lb) :
    switchRevenue 1 1 b lb 1 u 0 = b * (1 - Real.exp (-(lb * u))) := by
  unfold switchRevenue
  rw [expMin_of_nonneg _ _ (by norm_num), expMin_of_nonneg _ _ (by positivity)]
  simp [Eg_one, Eg_zero]

lemma sw0 (a la b lb t s : ℝ) : switchRevenue a la b lb 0 t s = 0 := by
  simp [switchRevenue, expMinPoisson]

lemma snm1 (u : ℝ) (hu : 0 ≤ u) :
    switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 u =
      max (3 / 4 * (1 - Real.exp (-(4 * u)))) (2 * (1 - Real.exp (-(1 / 20 * u)))) := by
  unfold switchNowMax
  rw [sw1 _ _ _ hu (by norm_num), sw1 _ _ _ hu (by norm_num)]

lemma snm1_mono (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 u ≤ switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 1 := by
  rw [snm1 u hu, snm1 1 zero_le_one]
  apply max_le_max
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply sub_le_sub_left
    apply Real.exp_le_exp.2
    linarith
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply sub_le_sub_left
    apply Real.exp_le_exp.2
    linarith

lemma snm1_nonneg : 0 ≤ switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 1 := by
  rw [snm1 1 zero_le_one]
  have := Real.exp_le_one_iff.2 (show -(4 * (1 : ℝ)) ≤ 0 by norm_num)
  refine le_max_of_le_left ?_
  norm_num at this ⊢

lemma G1 (t : ℝ) (ht : 0 ≤ t) : G 1 1 (3 / 4) 4 1 t = 1 / 4 - 9 / 4 * Real.exp (-(4 * t)) := by
  unfold G
  rw [poissonTail_eq, max_eq_left (by linarith)]
  simp [Tl, FF]
  ring

lemma log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

lemma log3_lt : Real.log 3 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith

lemma exp_x1 : Real.exp (-(4 * (Real.log 3 / 2))) = 1 / 9 := by
  rw [show -(4 * (Real.log 3 / 2)) = -(2 * Real.log 3) by ring, Real.exp_neg,
    show 2 * Real.log 3 = Real.log (3 ^ 2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by norm_num)]
  norm_num

lemma root_set (L : ℝ → ℝ) (hL : ∀ t, 0 ≤ t → L t = 1 / 4 - 9 / 4 * Real.exp (-(4 * t))) :
    {t : ℝ | 0 ≤ t ∧ L t = 0} = {Real.log 3 / 2} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ht, h⟩
    rw [hL t ht] at h
    have h2 : Real.exp (-(4 * t)) = Real.exp (-(4 * (Real.log 3 / 2))) := by
      rw [exp_x1]; linarith
    have := Real.exp_injective h2
    linarith
  · rintro rfl
    refine ⟨by linarith [log3_pos], ?_⟩
    rw [hL _ (by linarith [log3_pos]), exp_x1]
    norm_num

lemma H_pos (H : ℝ → ℝ) (L : ℝ → ℝ)
    (hL : ∀ t, 0 ≤ t → L t = 1 / 4 - 9 / 4 * Real.exp (-(4 * t)))
    (hd : ∀ t, 0 < t → HasDerivAt H (-1 * H t + L t) t)
    (hH : H (Real.log 3 / 2) = 0) : 0 < H 1 := by
  set x1 := Real.log 3 / 2 with hx1
  have hφ : ∀ t, 0 < t → HasDerivAt (fun t => Real.exp t * H t) (Real.exp t * L t) t := by
    intro t ht
    have h := (Real.hasDerivAt_exp t).mul (hd t ht)
    have he : Real.exp t * H t + Real.exp t * (-1 * H t + L t) = Real.exp t * L t := by ring
    rw [he] at h
    exact h
  have hx1pos : 0 < x1 := by rw [hx1]; linarith [log3_pos]
  have hx1lt : x1 < 1 := by rw [hx1]; linarith [log3_lt]
  have hmono : StrictMonoOn (fun t => Real.exp t * H t) (Set.Icc x1 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · intro t ht
      exact (hφ t (hx1pos.trans_le ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφ t (hx1pos.trans ht.1)).deriv]
      apply mul_pos (Real.exp_pos _)
      rw [hL t (by linarith [ht.1])]
      have : Real.exp (-(4 * t)) < 1 / 9 := by
        rw [← exp_x1]
        exact Real.exp_lt_exp.2 (by linarith [ht.1])
      linarith
  have := hmono ⟨le_rfl, hx1lt.le⟩ ⟨hx1lt.le, le_rfl⟩ hx1lt
  simp only [hH, mul_zero] at this
  exact pos_of_mul_pos_right this (Real.exp_pos 1).le

lemma payoff_le {τ : DP872.Ω0 → ℝ} (hτ : IsAdmissible DP872.P0 DP872.T0 1 1 τ) :
    ∫ ω, (1 * ((min 1 (countingProcess DP872.T0 (τ ω) ω) : ℕ) : ℝ)
      + switchNowMax (3 / 4) 4 1 1 2 (1 / 20) (1 - countingProcess DP872.T0 (τ ω) ω) (1 - τ ω))
        ∂DP872.P0
      ≤ switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 1 := by
  have : IsProbabilityMeasure DP872.P0 := DP872.P0_prob
  have hae : (fun ω => 1 * ((min 1 (countingProcess DP872.T0 (τ ω) ω) : ℕ) : ℝ)
      + switchNowMax (3 / 4) 4 1 1 2 (1 / 20) (1 - countingProcess DP872.T0 (τ ω) ω) (1 - τ ω))
      =ᵐ[DP872.P0] fun ω => switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 (1 - τ ω) := by
    filter_upwards [DP872.ae_cnt_zero hτ] with ω h
    rw [h]
    simp
  rw [integral_congr_ae hae]
  calc ∫ ω, switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 (1 - τ ω) ∂DP872.P0
      ≤ ∫ _ω, switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 1 ∂DP872.P0 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          (integrable_const _) (Filter.Eventually.of_forall fun ω => ?_)
        · have h1 := hτ.le_horizon ω
          simp only [Pi.zero_apply]
          rw [snm1 _ (by linarith)]
          have := Real.exp_le_one_iff.2 (show -(4 * (1 - τ ω)) ≤ 0 by linarith)
          exact le_max_of_le_left (by linarith)
        · have h0 := hτ.nonneg ω
          have h1 := hτ.le_horizon ω
          exact snm1_mono _ (by linarith) (by linarith)
    _ = switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 1 := by simp

lemma opt_le : optRevenue3 DP872.P0 DP872.T0 (3 / 4) 4 1 1 2 (1 / 20) 1 1
    ≤ switchNowMax (3 / 4) 4 1 1 2 (1 / 20) 1 1 := by
  unfold optRevenue3 stopValue
  exact Real.iSup_le (fun τ => payoff_le τ.2) snm1_nonneg

end DP3

open PriceSwitch.UpOrDown MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ → Ω → ℝ)
    (p₁ lam₁ p lam p₂ lam₂ : ℝ)
    (h3 : IsThreePrice p₁ lam₁ p lam p₂ lam₂)
    (hT : IsExpInterarrivals P lam T)
    (hassume : ∀ n : ℕ, 1 ≤ n →
      tThr1 p₁ lam₁ p lam p₂ lam₂ n < tThr p₁ lam₁ p lam p₂ lam₂ n ∧
      tThr p₁ lam₁ p lam p₂ lam₂ n < tThr2 p₁ lam₁ p lam p₂ lam₂ n),
    ∃ (x z : ℕ → ℝ) (F H₁ H₂ V : ℕ → ℝ → ℝ),
      let L₁ : ℕ → ℝ → ℝ := fun n t =>
        PriceSwitch.Markdown.G p lam p₁ lam₁ n t + lam * (V (n - 1) t - PriceSwitch.Markdown.switchRevenue p lam p₁ lam₁ (n - 1) t 0)
      let L₂ : ℕ → ℝ → ℝ := fun n t =>
        PriceSwitch.Markdown.G p lam p₂ lam₂ n t + lam * (V (n - 1) t - PriceSwitch.Markdown.switchRevenue p lam p₂ lam₂ (n - 1) t 0)
      StrictMonoOn x (Set.Ici 1) ∧ StrictMonoOn z (Set.Ici 1) ∧
      (∀ n, 1 ≤ n →
        x n < tThr1 p₁ lam₁ p lam p₂ lam₂ n ∧
        tThr1 p₁ lam₁ p lam p₂ lam₂ n < tThr p₁ lam₁ p lam p₂ lam₂ n ∧
        tThr p₁ lam₁ p lam p₂ lam₂ n < tThr2 p₁ lam₁ p lam p₂ lam₂ n ∧
        tThr2 p₁ lam₁ p lam p₂ lam₂ n < z n) ∧
      (∀ t, V 0 t = 0) ∧
      (∀ n, 1 ≤ n → ∀ t, V n t =
        if x n ≤ t ∧ t ≤ z n then switchNowMax p₁ lam₁ p lam p₂ lam₂ n t + F n t
        else switchNowMax p₁ lam₁ p lam p₂ lam₂ n t) ∧
      (∀ t, F 0 t = 0) ∧
      (∀ n, 1 ≤ n →
        (∀ t, 0 < t → HasDerivAt (H₁ n) (-lam * H₁ n t + L₁ n t) t) ∧
        H₁ n (x n) = 0 ∧
        (∀ t, 0 < t → HasDerivAt (H₂ n) (-lam * H₂ n t + L₂ n t) t) ∧
        H₂ n (tThr p₁ lam₁ p lam p₂ lam₂ n) = H₁ n (tThr p₁ lam₁ p lam p₂ lam₂ n) ∧
        (∃ t, 0 ≤ t ∧ L₁ n t = 0) ∧
        x n = sInf {t : ℝ | 0 ≤ t ∧ L₁ n t = 0} ∧
        (∃ t, tThr p₁ lam₁ p lam p₂ lam₂ n ≤ t ∧ H₂ n t ≤ 0) ∧
        z n = sInf {t : ℝ | tThr p₁ lam₁ p lam p₂ lam₂ n ≤ t ∧ H₂ n t ≤ 0} ∧
        (∀ t, F n t =
          if x n ≤ t ∧ t ≤ tThr p₁ lam₁ p lam p₂ lam₂ n then H₁ n t
          else if tThr p₁ lam₁ p lam p₂ lam₂ n ≤ t ∧ t ≤ z n then H₂ n t
          else 0)) ∧
      (∀ n t, 0 ≤ t → optRevenue3 P T p₁ lam₁ p lam p₂ lam₂ n t = V n t)) := by
  intro h
  obtain ⟨x, z, F, H₁, H₂, V, hrest⟩ :=
    @h DP872.Ω0 _ DP872.P0 DP872.P0_prob DP872.T0 (3 / 4) 4 1 1 2 (1 / 20) DP3.three DP872.hT0
      DP3.hassume_holds
  obtain ⟨-, -, hord, hV0, hV, -, hn, hopt⟩ := hrest
  obtain ⟨hd1, hH1x, -, -, -, hxeq, -, -, hFd⟩ := hn 1 le_rfl
  obtain ⟨hx1, h12, h23, h3z⟩ := hord 1 le_rfl
  have ht1 := DP3.tThr1_one_gt
  have hL : ∀ t, 0 ≤ t →
      (PriceSwitch.Markdown.G 1 1 (3 / 4) 4 1 t + 1 * (V (1 - 1) t -
        PriceSwitch.Markdown.switchRevenue 1 1 (3 / 4) 4 (1 - 1) t 0))
        = 1 / 4 - 9 / 4 * Real.exp (-(4 * t)) := by
    intro t ht
    rw [Nat.sub_self, hV0, DP3.sw0, DP3.G1 t ht]
    ring
  have hset := DP3.root_set _ hL
  simp only at hxeq
  rw [hset, csInf_singleton] at hxeq
  have hd1' : ∀ t, 0 < t → HasDerivAt (H₁ 1) (-1 * H₁ 1 t +
      (PriceSwitch.Markdown.G 1 1 (3 / 4) 4 1 t + 1 * (V (1 - 1) t -
        PriceSwitch.Markdown.switchRevenue 1 1 (3 / 4) 4 (1 - 1) t 0))) t := by
    intro t ht
    exact hd1 t ht
  rw [hxeq] at hH1x
  have hpos := DP3.H_pos (H₁ 1) _ hL hd1' hH1x
  have hx1lt : x 1 ≤ 1 := by rw [hxeq]; linarith [DP3.log3_lt]
  have hval := hopt 1 1 zero_le_one
  rw [hV 1 le_rfl 1, if_pos ⟨hx1lt, by linarith⟩, hFd 1, if_pos ⟨hx1lt, by linarith⟩] at hval
  have hle := DP3.opt_le
  linarith

