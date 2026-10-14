-- Prove2me | solution 1 for PriceSwitch.UpOrDown.lemma3_markdown
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:25:25.369586+00:00
-- url     : https://prove2.me/submissions/649e834d-afcb-4e22-ab5f-5e44aa08be88

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

open PriceSwitch.Markdown
open Filter Topology

namespace PriceSwitch.UpOrDown

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

end PriceSwitch.UpOrDown

open PriceSwitch.UpOrDown


theorem solution (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkdownPair a la b lb) :
    let Δ : ℕ → ℝ → ℝ := fun n t => PriceSwitch.Markdown.switchRevenue a la b lb n t t - PriceSwitch.Markdown.switchRevenue a la b lb n t 0
    let tn : ℕ → ℝ := fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < tn n → Δ n t < 0) ∧
    (∀ n, 1 ≤ n → ∀ t, tn n < t → 0 < Δ n t) ∧
    StrictMonoOn tn (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → MonotoneOn (Δ n) (Set.Ioi (tn n))) ∧
    (∀ n, 1 ≤ n → Tendsto (Δ n) atTop (𝓝 ((a - b) * n))) := by
  exact lemma3_markdown_core a la b lb hpair
