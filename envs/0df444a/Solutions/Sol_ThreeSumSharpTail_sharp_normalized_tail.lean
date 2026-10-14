-- Prove2me | solution 1 for ThreeSumSharpTail.sharp_normalized_tail
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T15:46:49.626524+00:00
-- url     : https://prove2.me/submissions/d469e187-401e-4cfa-9dfb-0b0969e4d5db

import Theorems.Thm_ThreeSumSharpTail_binomial_entropy_bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
open Set

namespace ThreeSumSharpTail

/-- One step of the box-count tail decays by at least the factor `9/(c-1)`. -/
theorem boxCount_step (c m d : ℕ) (hc : 10 < c) (hd : 1 ≤ d) (hdm : d ≤ m) :
    ((c - 1 : ℕ) : ℝ) * boxCount c m d ≤ 9 * boxCount c m (d - 1) := by
  have hchoose := Nat.choose_succ_right_eq (c * m) (m - d)
  have hexp : c * m - m + d = (c * m - m + (d - 1)) + 1 := by omega
  have hidx : m - (d - 1) = m - d + 1 := by omega
  rw [boxCount, boxCount, hidx, hexp]
  push_cast
  rw [pow_succ]
  have hmul := congrArg (fun z : ℕ => (z : ℝ)) hchoose
  push_cast at hmul
  have hden : (c * m : ℝ) - ((m - d : ℕ) : ℝ) =
      ((c - 1 : ℕ) : ℝ) * m + d := by
    rw [Nat.cast_sub hdm, Nat.cast_sub (by omega : 1 ≤ c)]
    ring
  have hdineq : ((c - 1 : ℕ) : ℝ) * ((m - d + 1 : ℕ) : ℝ) ≤
      ((c * m : ℝ) - ((m - d : ℕ) : ℝ)) := by
    have hmd : (d : ℝ) ≤ m := by exact_mod_cast hdm
    have hdpos : (0 : ℝ) ≤ d := by positivity
    have hc1 : (1 : ℝ) ≤ (c : ℝ) - 1 := by
      have hcR : (2 : ℝ) ≤ c := by exact_mod_cast (show 2 ≤ c by omega)
      linarith
    have hcast : ((m - d + 1 : ℕ) : ℝ) = (m : ℝ) - d + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hdm]
      norm_num
    rw [hcast]
    rw [hden]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hkbound : (m : ℝ) - d + 1 ≤ m := by linarith
    have hprod := mul_le_mul_of_nonneg_left hkbound (by positivity : 0 ≤ (c : ℝ) - 1)
    nlinarith
  have hnonneg : 0 ≤ (Nat.choose (c * m) (m - d) : ℝ) := by positivity
  have hpow : 0 ≤ (9 : ℝ) ^ (c * m - m + (d - 1)) := by positivity
  have hmult := mul_le_mul_of_nonneg_left hdineq (show 0 ≤ (Nat.choose (c * m) (m - d) : ℝ) by positivity)
  have hmul' : (Nat.choose (c * m) (m - d + 1) : ℝ) * ((m - d + 1 : ℕ) : ℝ) =
      (Nat.choose (c * m) (m - d) : ℝ) * ((c * m : ℝ) - ((m - d : ℕ) : ℝ)) := by
    rw [Nat.cast_add]
    have hbound : m - d ≤ c * m := by
      have hmle : m ≤ c * m := Nat.le_mul_of_pos_left m (by omega : 0 < c)
      omega
    have hcastSub : ((c * m - (m - d) : ℕ) : ℝ) =
        (c * m : ℝ) - ((m - d : ℕ) : ℝ) := by
      rw [Nat.cast_sub hbound]
      push_cast
      ring
    rw [← hcastSub]
    simpa using hmul
  have hpos : 0 < ((m - d + 1 : ℕ) : ℝ) := by positivity
  have hcoeff : ((c - 1 : ℕ) : ℝ) * (Nat.choose (c * m) (m - d) : ℝ) ≤
      (Nat.choose (c * m) (m - d + 1) : ℝ) := by
    nlinarith [hmul', hmult]
  have hscale := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ 9 * (9 : ℝ) ^ (c * m - m + (d - 1)) by positivity)
  nlinarith [hscale]



lemma entropy_eq_binEntropy (x : ℝ) : entropy x = Real.binEntropy x := by
  unfold entropy Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

noncomputable def tailProfile (c u : ℝ) : ℝ :=
  c * Real.binEntropy ((1 - u) / c) + u * Real.log 9

lemma tailProfile_continuous (c : ℝ) : Continuous (tailProfile c) := by
  unfold tailProfile
  fun_prop

lemma tailProfile_hasDerivAt {c u : ℝ} (hc : 10 < c) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (tailProfile c)
      (c * ((Real.log (1 - (1 - u) / c) - Real.log ((1 - u) / c)) * (-1 / c)) + Real.log 9) u := by
  have hcpos : 0 < c := by linarith
  have hp : 0 < (1 - u) / c := div_pos (by linarith) hcpos
  have hp1 : (1 - u) / c < 1 := by
    rw [div_lt_one hcpos]
    linarith
  have hlin : HasDerivAt (fun v : ℝ => (1 - v) / c) (-1 / c) u := by
    simpa using ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).div_const c
  have hbin := (Real.hasDerivAt_binEntropy hp.ne' hp1.ne).comp u hlin
  unfold tailProfile
  convert (hbin.const_mul c).add ((hasDerivAt_id u).mul_const (Real.log 9)) using 1 <;>
    (first | ext v <;> dsimp <;> field_simp <;> ring | field_simp <;> ring)

/-- The entropy plus `log 9` profile is antitone on the full parameter interval. -/
theorem tail_profile_antitone (c : ℝ) (hc : 10 < c) :
    AntitoneOn (fun u => c * entropy ((1 - u) / c) + u * Real.log 9) (Icc 0 1) := by
  have hEq : (fun u => c * entropy ((1 - u) / c) + u * Real.log 9) = tailProfile c := by
    funext u
    simp [tailProfile, entropy_eq_binEntropy]
  rw [hEq]
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · exact (tailProfile_continuous c).continuousOn
  · intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hu
    obtain ⟨hu0, hu1⟩ := hu'
    exact (tailProfile_hasDerivAt hc hu0 hu1).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hu
    obtain ⟨hu0, hu1⟩ := hu'
    have hF := tailProfile_hasDerivAt hc hu0 hu1
    rw [hF.deriv]
    let p : ℝ := (1 - u) / c
    have hp : 0 < p := by dsimp [p]; positivity
    have hq : 0 < 1 - p := by
      dsimp [p]
      have hcpos : 0 < c := by linarith
      have hlt : (1 - u) / c < 1 := by rw [div_lt_one hcpos]; linarith
      linarith
    have hsmall : 9 * p < 1 - p := by
      dsimp [p]
      have hcpos : 0 < c := by linarith
      have hnum : 9 * (1 - u) < c - 1 + u := by nlinarith [hc, hu0]
      have hscaled : 9 * (1 - u) / c < (c - 1 + u) / c :=
        (div_lt_div_iff₀ hcpos hcpos).2 (by nlinarith)
      have hqeq : 1 - (1 - u) / c = (c - 1 + u) / c := by field_simp; ring
      rw [hqeq]
      convert hscaled using 1 <;> ring
    have hlog : Real.log (9 * p) < Real.log (1 - p) := Real.log_lt_log (by positivity) hsmall
    have hderiv : c * ((Real.log (1 - p) - Real.log p) * (-1 / c)) + Real.log 9 =
        Real.log (9 * p) - Real.log (1 - p) := by
      have hcne : c ≠ 0 := ne_of_gt (by linarith : 0 < c)
      rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) hp.ne']
      dsimp [p]
      field_simp
      ring
    rw [hderiv]
    linarith


lemma geometric_partial_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, ρ ^ i) ≤ 1 / (1 - ρ) := by
  have h := geom_sum_mul ρ n
  apply (le_div_iff₀ (by linarith : 0 < 1 - ρ)).2
  nlinarith [pow_nonneg hρ0 n]

lemma boxCount_sum_le (c m t : ℕ) (hc : 10 < c) (_htm : t ≤ m) :
    (∑ d ∈ Finset.Icc t m, (boxCount c m d : ℝ)) ≤
      (boxCount c m t : ℝ) / (1 - 9 / ((c : ℝ) - 1)) := by
  let ρ : ℝ := 9 / ((c : ℝ) - 1)
  have hcR : (10 : ℝ) < c := by exact_mod_cast hc
  have hcp : 0 < (c : ℝ) - 1 := by linarith
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := (div_lt_one hcp).2 (by linarith)
  have hbound : ∀ d, t ≤ d → d ≤ m →
      (boxCount c m d : ℝ) ≤ (boxCount c m t : ℝ) * ρ ^ (d - t) := by
    intro d htd hdm
    induction d, htd using Nat.le_induction with
    | base => simp
    | succ d htd ih =>
      have hstep := boxCount_step c m (d + 1) hc (by omega) hdm
      rw [Nat.add_sub_cancel, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one] at hstep
      have hs : (boxCount c m (d + 1) : ℝ) ≤ ρ * (boxCount c m d : ℝ) := by
        dsimp [ρ]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hcp).2
        simpa [mul_comm] using hstep
      calc
        _ ≤ ρ * ((boxCount c m t : ℝ) * ρ ^ (d - t)) :=
          hs.trans (mul_le_mul_of_nonneg_left (ih (by omega)) hρ0)
        _ = _ := by rw [show d + 1 - t = d - t + 1 by omega, pow_succ]; ring
  have hsum : (∑ d ∈ Finset.Icc t m, ρ ^ (d - t)) =
      ∑ i ∈ Finset.range (m + 1 - t), ρ ^ i := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range (fun d => ρ ^ (d - t))]
    simp
  calc
    _ ≤ ∑ d ∈ Finset.Icc t m, (boxCount c m t : ℝ) * ρ ^ (d - t) :=
      Finset.sum_le_sum fun d hd => hbound d (Finset.mem_Icc.1 hd).1 (Finset.mem_Icc.1 hd).2
    _ = (boxCount c m t : ℝ) * ∑ i ∈ Finset.range (m + 1 - t), ρ ^ i := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ (boxCount c m t : ℝ) * (1 / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left (geometric_partial_le ρ hρ0 hρ1 _) (Nat.cast_nonneg _)
    _ = _ := by dsimp [ρ]; ring

lemma boxCount_ratio_entropy (c m t : ℕ) (hc : 10 < c) (hm : 1 ≤ m) (_ht : t ≤ m) :
    (boxCount c m t : ℝ) / (boxCount c m 0 : ℝ) ≤
      ((c * m : ℕ) + 1 : ℝ) * Real.exp
        ((c * m : ℕ) * entropy ((m - t : ℕ) / (c * m : ℕ)) -
          (c * m : ℕ) * entropy ((m : ℝ) / (c * m : ℕ)) + t * Real.log 9) := by
  have hmL : m ≤ c * m := Nat.le_mul_of_pos_left m (by omega)
  have hL : 1 ≤ c * m := hm.trans hmL
  have hct : m - t ≤ c * m := (Nat.sub_le m t).trans hmL
  have hzero := binomial_entropy_bounds (c * m) m hL hmL
  have htop := binomial_entropy_bounds (c * m) (m - t) hL hct
  have hchoose : 0 < (Nat.choose (c * m) m : ℝ) := by
    exact_mod_cast Nat.choose_pos hmL
  have hpow : 0 < (9 : ℝ) ^ (c * m - m) := pow_pos (by norm_num) _
  have hden : 0 < ((c * m : ℕ) + 1 : ℝ) := by positivity
  have hr := div_le_div₀ (Real.exp_pos _).le
    htop.2 (div_pos (Real.exp_pos _) hden) hzero.1
  calc
    _ = ((Nat.choose (c * m) (m - t) : ℝ) / (Nat.choose (c * m) m : ℝ)) *
        (9 : ℝ) ^ t := by
      simp only [boxCount, Nat.sub_zero, add_zero, Nat.cast_mul, Nat.cast_pow,
        pow_add]
      field_simp
      norm_num
    _ ≤ (Real.exp ((c * m : ℕ) * entropy ((m - t : ℕ) / (c * m : ℕ))) /
        (Real.exp ((c * m : ℕ) * entropy ((m : ℝ) / (c * m : ℕ))) /
          ((c * m : ℕ) + 1 : ℝ))) * (9 : ℝ) ^ t :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by
      have hexp9 : Real.exp ((t : ℝ) * Real.log 9) = (9 : ℝ) ^ t := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 9)]
      rw [Real.exp_add, Real.exp_sub, hexp9]
      field_simp

end ThreeSumSharpTail

theorem solution (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    ((∑ d ∈ Finset.Icc (⌈θ * (m : ℝ)⌉₊) m, ThreeSumSharpTail.boxCount c m d : ℕ) : ℝ) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      ((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ) := by
  let t : ℕ := ⌈θ * (m : ℝ)⌉₊
  let u : ℝ := (t : ℝ) / m
  have hcR : (10 : ℝ) < c := by exact_mod_cast hc
  have hcp : 0 < (c : ℝ) := by linarith
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hθ1 : θ < 1 := by linarith
  have ht : t ≤ m := Nat.ceil_le.2 (by nlinarith)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := (div_le_one hmR).2 (by exact_mod_cast ht)
  have hθu : θ ≤ u := (le_div_iff₀ hmR).2 (Nat.le_ceil _)
  have hanti := ThreeSumSharpTail.tail_profile_antitone (c : ℝ) hcR
    (show θ ∈ Set.Icc (0 : ℝ) 1 from ⟨hθ0.le, hθ1.le⟩)
    (show u ∈ Set.Icc (0 : ℝ) 1 from ⟨hu0, hu1⟩) hθu
  have hdiv0 : (m : ℝ) / (c * m : ℕ) = 1 / (c : ℝ) := by
    rw [Nat.cast_mul]
    field_simp
  have hdivt : ((m - t : ℕ) : ℝ) / (c * m : ℕ) = (1 - u) / (c : ℝ) := by
    rw [Nat.cast_sub ht, Nat.cast_mul]
    dsimp [u]
    field_simp
  have htu : (m : ℝ) * u = t := by dsimp [u]; field_simp
  have hExponent :
      (c * m : ℕ) * ThreeSumSharpTail.entropy ((m - t : ℕ) / (c * m : ℕ)) -
        (c * m : ℕ) * ThreeSumSharpTail.entropy ((m : ℝ) / (c * m : ℕ)) + t * Real.log 9 ≤
      (m : ℝ) * ((c : ℝ) * ThreeSumSharpTail.entropy ((1 - θ) / c) +
        θ * Real.log 9 - (c : ℝ) * ThreeSumSharpTail.entropy (1 / c)) := by
    rw [hdiv0, hdivt, Nat.cast_mul, ← htu]
    nlinarith [mul_le_mul_of_nonneg_left hanti hmR.le]
  have hExp :
      Real.exp ((m : ℝ) * ((c : ℝ) * ThreeSumSharpTail.entropy ((1 - θ) / c) +
        θ * Real.log 9 - (c : ℝ) * ThreeSumSharpTail.entropy (1 / c))) =
      Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    unfold ThreeSumSharpTail.sharpSaving
    congr 1
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))]
    ring
  have hfirst : (ThreeSumSharpTail.boxCount c m t : ℝ) /
      (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      ((c * m : ℕ) + 1 : ℝ) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ) := by
    have h := (ThreeSumSharpTail.boxCount_ratio_entropy c m t hc hm ht).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hExponent)
        (by positivity : (0 : ℝ) ≤ (c * m : ℕ) + 1))
    rwa [hExp] at h
  have hmL : m ≤ c * m := Nat.le_mul_of_pos_left m (by omega)
  have hden0 : 0 < (ThreeSumSharpTail.boxCount c m 0 : ℝ) := by
    unfold ThreeSumSharpTail.boxCount
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hmL) (by positivity)
  have hρden : 0 < 1 - 9 / ((c : ℝ) - 1) := by
    have hratio : 9 / ((c : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith : 0 < (c : ℝ) - 1)).2 (by linarith)
    linarith
  have hsum := ThreeSumSharpTail.boxCount_sum_le c m t hc ht
  change ((∑ d ∈ Finset.Icc t m, ThreeSumSharpTail.boxCount c m d : ℕ) : ℝ) /
      (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤ _
  rw [Nat.cast_sum]
  calc
    _ ≤ ((ThreeSumSharpTail.boxCount c m t : ℝ) / (1 - 9 / ((c : ℝ) - 1))) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ) :=
      div_le_div_of_nonneg_right hsum hden0.le
    _ = ((ThreeSumSharpTail.boxCount c m t : ℝ) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ)) / (1 - 9 / ((c : ℝ) - 1)) := by ring
    _ ≤ (((c * m : ℕ) + 1 : ℝ) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) /
          (1 - 9 / ((c : ℝ) - 1)) :=
      (div_le_div_iff_of_pos_right hρden).2 hfirst
    _ = _ := by push_cast; ring

#print axioms solution
