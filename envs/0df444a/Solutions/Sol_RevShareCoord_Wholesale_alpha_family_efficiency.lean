-- Prove2me | solution 1 for RevShareCoord.Wholesale.alpha_family_efficiency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:28:51.874563+00:00
-- url     : https://prove2.me/submissions/d64b4374-daec-451e-8667-ff3de079dbdb

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

set_option autoImplicit false

namespace AlphaAuxE5F6

open RevShareCoord.Wholesale Filter Topology

lemma alphaRevenue_eq (α : ℝ) : alphaRevenue α = fun q => q - q ^ (α + 1) / (α + 1) := by
  funext q; rfl

lemma deriv_alphaRevenue (α : ℝ) (hα : 0 < α) (q : ℝ) :
    deriv (alphaRevenue α) q = 1 - q ^ α := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (α + 1)) ((α + 1) * q ^ (α + 1 - 1)) q :=
    Real.hasDerivAt_rpow_const (Or.inr (by linarith))
  have h2 : HasDerivAt (alphaRevenue α) (1 - (α + 1) * q ^ (α + 1 - 1) / (α + 1)) q := by
    rw [alphaRevenue_eq]
    exact (hasDerivAt_id q).sub (h1.div_const (α + 1))
  rw [h2.deriv]
  have : α + 1 - 1 = α := by ring
  rw [this]
  field_simp

/-- tangent-line inequality for `x ^ (β+1)` -/
lemma tangent_lt (β : ℝ) (hβ : 0 < β) (s q : ℝ) (hs : 0 < s) (hq : 0 ≤ q) (hne : q ≠ s) :
    s ^ (β + 1) + (β + 1) * s ^ β * (q - s) < q ^ (β + 1) := by
  have ht : -1 ≤ q / s - 1 := by
    have : 0 ≤ q / s := div_nonneg hq hs.le
    linarith
  have ht0 : q / s - 1 ≠ 0 := by
    intro h
    apply hne
    have : q / s = 1 := by linarith
    field_simp at this
    linarith
  have key := one_add_mul_self_lt_rpow_one_add ht ht0 (p := β + 1) (by linarith)
  have e1 : (1 + (q / s - 1)) = q / s := by ring
  rw [e1, Real.div_rpow hq hs.le] at key
  have hsp : 0 < s ^ (β + 1) := Real.rpow_pos_of_pos hs _
  have e2 : s ^ (β + 1) = s ^ β * s := Real.rpow_add_one hs.ne' β
  rw [lt_div_iff₀ hsp] at key
  rw [e2] at key ⊢
  have : (1 + (β + 1) * (q / s - 1)) * (s ^ β * s) = s ^ β * s + (β + 1) * s ^ β * (q - s) := by
    field_simp
  linarith

lemma pow_alpha_of_root (α k : ℝ) (hα : 0 < α) (hk : 0 ≤ k) : (k ^ (1 / α)) ^ α = k := by
  rw [← Real.rpow_mul hk]
  have : 1 / α * α = 1 := by field_simp
  rw [this, Real.rpow_one]

lemma mem_Icc_root (α k : ℝ) (hα : 0 < α) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    k ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.rpow_nonneg hk0 _, Real.rpow_le_one hk0 hk1 (by positivity)⟩

lemma supplier_eq (α c q : ℝ) (hα : 0 < α) (hq : 0 ≤ q) :
    supplierProfit (deriv (alphaRevenue α)) c q = q * (1 - c) - q ^ (α + 1) := by
  unfold supplierProfit inducingPrice
  rw [deriv_alphaRevenue α hα, Real.rpow_add_one' hq (by linarith)]
  ring

lemma chain_eq (α c q : ℝ) :
    chainProfit (alphaRevenue α) c q = q * (1 - c) - q ^ (α + 1) / (α + 1) := by
  unfold chainProfit alphaRevenue
  ring

lemma supplier_part (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
    (((1 - c) / (1 + α)) ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (supplierProfit (deriv (alphaRevenue α)) c) (Set.Icc 0 1)
        (((1 - c) / (1 + α)) ^ (1 / α)) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (supplierProfit (deriv (alphaRevenue α)) c) (Set.Icc 0 1) q →
          q = ((1 - c) / (1 + α)) ^ (1 / α)) := by
  set k := (1 - c) / (1 + α) with hk
  have hk0 : 0 < k := by rw [hk]; apply div_pos <;> linarith
  have hk1 : k ≤ 1 := by
    rw [hk, div_le_one (by linarith)]; linarith
  set s := k ^ (1 / α) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hk0 _
  have hsα : s ^ α = k := pow_alpha_of_root α k hα hk0.le
  have hmem : s ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_root α k hα hk0.le hk1
  -- strict inequality off s
  have hlt : ∀ q, 0 ≤ q → q ≠ s →
      supplierProfit (deriv (alphaRevenue α)) c q < supplierProfit (deriv (alphaRevenue α)) c s := by
    intro q hq hne
    rw [supplier_eq α c q hα hq, supplier_eq α c s hα hs.le]
    have h := tangent_lt α hα s q hs hq hne
    rw [hsα] at h
    have hk' : (α + 1) * k = 1 - c := by
      rw [hk]; field_simp; ring
    have : (α + 1) * k * (q - s) = (1 - c) * (q - s) := by rw [hk']
    nlinarith
  refine ⟨hmem, ?_, ?_⟩
  · intro q hq
    by_cases hqs : q = s
    · rw [hqs]; simp
    · exact (hlt q hq.1 hqs).le
  · intro q hq hmax
    by_contra hne
    have h1 := hlt q hq.1 hne
    have h2 := hmax hmem
    exact absurd h2 (not_le.mpr h1)

lemma chain_part (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
    ((1 - c) ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (chainProfit (alphaRevenue α) c) (Set.Icc 0 1) ((1 - c) ^ (1 / α)) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (chainProfit (alphaRevenue α) c) (Set.Icc 0 1) q → q = (1 - c) ^ (1 / α)) := by
  have hk0 : 0 < 1 - c := by linarith
  have hk1 : 1 - c ≤ 1 := by linarith
  set s := (1 - c) ^ (1 / α) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hk0 _
  have hsα : s ^ α = 1 - c := pow_alpha_of_root α (1 - c) hα hk0.le
  have hmem : s ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_root α (1 - c) hα hk0.le hk1
  have hlt : ∀ q, 0 ≤ q → q ≠ s →
      chainProfit (alphaRevenue α) c q < chainProfit (alphaRevenue α) c s := by
    intro q hq hne
    rw [chain_eq, chain_eq]
    have h := tangent_lt α hα s q hs hq hne
    rw [hsα] at h
    have ha1 : 0 < α + 1 := by linarith
    rw [sub_lt_sub_iff, ← sub_pos]
    have : s * (1 - c) + q ^ (α + 1) / (α + 1) - (q * (1 - c) + s ^ (α + 1) / (α + 1))
        = (q ^ (α + 1) - (s ^ (α + 1) + (α + 1) * (1 - c) * (q - s))) / (α + 1) := by
      field_simp
      ring
    rw [this]
    apply div_pos _ ha1
    linarith
  refine ⟨hmem, ?_, ?_⟩
  · intro q hq
    by_cases hqs : q = s
    · rw [hqs]; simp
    · exact (hlt q hq.1 hqs).le
  · intro q hq hmax
    by_contra hne
    have h1 := hlt q hq.1 hne
    have h2 := hmax hmem
    exact absurd h2 (not_le.mpr h1)

lemma share_part (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
    profitShare (alphaRevenue α) (deriv (alphaRevenue α)) c (((1 - c) / (1 + α)) ^ (1 / α)) =
      (1 + α) / (2 + α) := by
  set k := (1 - c) / (1 + α) with hk
  have hk0 : 0 < k := by rw [hk]; apply div_pos <;> linarith
  set s := k ^ (1 / α) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hk0 _
  have hsα : s ^ α = k := pow_alpha_of_root α k hα hk0.le
  unfold profitShare
  rw [supplier_eq α c s hα hs.le, chain_eq, Real.rpow_add_one hs.ne', hsα, hk]
  have h1 : (1 : ℝ) - c ≠ 0 := by linarith
  have h2 : (1 : ℝ) + α ≠ 0 := by linarith
  have h3 : (2 : ℝ) + α ≠ 0 := by linarith
  have h4 : α + 1 ≠ 0 := by linarith
  have hne : s * (1 - c) - (1 - c) / (1 + α) * s / (α + 1) ≠ 0 := by
    have : s * (1 - c) - (1 - c) / (1 + α) * s / (α + 1)
        = s * (1 - c) * (α * (2 + α)) / ((1 + α) * (1 + α)) := by
      field_simp; ring
    rw [this]
    have : 0 < 1 - c := by linarith
    positivity
  rw [div_eq_div_iff hne h3]
  field_simp
  ring

/-- closed form in exp/log -/
noncomputable def F (a : ℝ) : ℝ := (2 + a) / (1 + a) * Real.exp (-(Real.log (1 + a) / a))

lemma eff_closed (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
    alphaEfficiency α c = (2 + α) / (1 + α) ^ ((1 + α) / α) := by
  unfold alphaEfficiency efficiency
  set k := (1 - c) / (1 + α) with hk
  have hk0 : 0 < k := by rw [hk]; apply div_pos <;> linarith
  have hc' : 0 < 1 - c := by linarith
  set s := k ^ (1 / α) with hsdef
  set t := (1 - c) ^ (1 / α) with htdef
  have hs : 0 < s := Real.rpow_pos_of_pos hk0 _
  have ht : 0 < t := Real.rpow_pos_of_pos hc' _
  have hsα : s ^ α = k := pow_alpha_of_root α k hα hk0.le
  have htα : t ^ α = 1 - c := pow_alpha_of_root α (1 - c) hα hc'.le
  set u := (1 + α) ^ (1 / α) with hudef
  have hu : 0 < u := Real.rpow_pos_of_pos (by linarith) _
  have hst : s = t / u := by
    rw [hsdef, hk, Real.div_rpow hc'.le (by linarith)]
  have hpow : (1 + α) ^ ((1 + α) / α) = u * (1 + α) := by
    have : (1 + α) / α = 1 / α + 1 := by field_simp
    rw [this, Real.rpow_add_one (by linarith)]
  rw [hpow]
  rw [supplier_eq α c s hα hs.le, chain_eq]
  unfold retailerProfit inducingPrice
  rw [deriv_alphaRevenue α hα, alphaRevenue_eq]
  simp only
  rw [Real.rpow_add_one hs.ne', Real.rpow_add_one ht.ne', hsα, htα, hk, hst]
  have h1 : (1 : ℝ) - c ≠ 0 := by linarith
  have h2 : (1 : ℝ) + α ≠ 0 := by linarith
  have h4 : α + 1 ≠ 0 := by linarith
  have hden : t * (1 - c) - (1 - c) * t / (α + 1) ≠ 0 := by
    have : t * (1 - c) - (1 - c) * t / (α + 1) = t * (1 - c) * α / (α + 1) := by
      field_simp; ring
    rw [this]; positivity
  rw [div_eq_div_iff hden (by positivity)]
  field_simp
  ring

lemma closed_eq_F (a : ℝ) (ha : 0 < a) : (2 + a) / (1 + a) ^ ((1 + a) / a) = F a := by
  unfold F
  have h1 : 0 < 1 + a := by linarith
  rw [Real.rpow_def_of_pos h1]
  have : Real.log (1 + a) * ((1 + a) / a) = Real.log (1 + a) + Real.log (1 + a) / a := by
    field_simp
    ring
  rw [this, Real.exp_add, Real.exp_log h1, Real.exp_neg]
  field_simp

lemma eff_eq_F (a c : ℝ) (ha : 0 < a) (hc0 : 0 < c) (hc1 : c < 1) :
    alphaEfficiency a c = F a := by
  rw [eff_closed a c ha hc0 hc1, closed_eq_F a ha]

/-- `F = exp ∘ h` -/
noncomputable def hfun (a : ℝ) : ℝ :=
  Real.log (2 + a) - Real.log (1 + a) - Real.log (1 + a) / a

lemma F_eq_exp_h (a : ℝ) (ha : 0 < a) : F a = Real.exp (hfun a) := by
  unfold F hfun
  rw [sub_eq_add_neg _ (Real.log (1 + a) / a), Real.exp_add, Real.exp_sub,
    Real.exp_log (by linarith), Real.exp_log (by linarith)]

lemma h_hasDeriv (a : ℝ) (ha : 0 < a) :
    HasDerivAt hfun (1 / (2 + a) - 1 / (1 + a) -
      ((1 / (1 + a)) * a - Real.log (1 + a) * 1) / a ^ 2) a := by
  have d2 : HasDerivAt (fun x : ℝ => Real.log (2 + x)) (1 / (2 + a)) a := by
    have := ((hasDerivAt_id a).const_add 2).log (by simp; linarith)
    simpa using this
  have d1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + a)) a := by
    have := ((hasDerivAt_id a).const_add 1).log (by simp; linarith)
    simpa using this
  have d3 := d1.div (hasDerivAt_id a) ha.ne'
  have e : hfun = fun x => Real.log (2 + x) - Real.log (1 + x) - Real.log (1 + x) / x := rfl
  rw [e]
  exact (d2.sub d1).sub d3

lemma h_strictMono : StrictMonoOn hfun (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (h_hasDeriv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : 0 < x := hx
    rw [(h_hasDeriv x hx').deriv]
    have hl := Real.lt_log_one_add_of_pos hx'
    set ℓ := Real.log (1 + x)
    have e : 1 / (2 + x) - 1 / (1 + x) - ((1 / (1 + x)) * x - ℓ * 1) / x ^ 2
        = (ℓ * (2 + x) - 2 * x) / (x ^ 2 * (2 + x)) := by
      field_simp
      ring
    rw [e]
    apply div_pos _ (by positivity)
    rw [div_lt_iff₀ (by linarith)] at hl
    linarith

lemma F_strictMono : StrictMonoOn F (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [F_eq_exp_h x hx, F_eq_exp_h y hy]
  exact Real.exp_lt_exp.mpr (h_strictMono hx hy hxy)

lemma L_tendsto_zero :
    Tendsto (fun a : ℝ => Real.log (1 + a) / a) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.log (1 : ℝ)⁻¹ 1 := Real.hasDerivAt_log one_ne_zero
  have := hd.tendsto_slope_zero_right
  simp only [inv_one, Real.log_one, sub_zero, smul_eq_mul] at this
  refine this.congr' ?_
  filter_upwards with t
  rw [add_comm, div_eq_inv_mul]

lemma L_tendsto_top :
    Tendsto (fun a : ℝ => Real.log (1 + a) / a) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h1 : Tendsto (fun a : ℝ => 1 + a) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have := h0.comp h1
  refine this.congr' ?_
  filter_upwards with t
  simp

lemma F_tendsto_zero : Tendsto F (𝓝[>] 0) (𝓝 (2 / Real.exp 1)) := by
  have hq : Tendsto (fun a : ℝ => (2 + a) / (1 + a)) (𝓝[>] 0) (𝓝 ((2 + 0) / (1 + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Tendsto.div
    · exact tendsto_const_nhds.add tendsto_id
    · exact tendsto_const_nhds.add tendsto_id
    · norm_num
  have he : Tendsto (fun a : ℝ => Real.exp (-(Real.log (1 + a) / a))) (𝓝[>] 0)
      (𝓝 (Real.exp (-1))) :=
    (Real.continuous_exp.tendsto _).comp L_tendsto_zero.neg
  have := hq.mul he
  rw [Real.exp_neg] at this
  have e : F = fun a => (2 + a) / (1 + a) * Real.exp (-(Real.log (1 + a) / a)) := rfl
  rw [e, show (2 : ℝ) / Real.exp 1 = (2 + 0) / (1 + 0) * (Real.exp 1)⁻¹ by
    norm_num [div_eq_mul_inv]]
  exact this

lemma F_tendsto_top : Tendsto F atTop (𝓝 1) := by
  have hq : Tendsto (fun a : ℝ => 1 + (1 + a)⁻¹) atTop (𝓝 (1 + 0)) := by
    apply tendsto_const_nhds.add
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
  have he : Tendsto (fun a : ℝ => Real.exp (-(Real.log (1 + a) / a))) atTop
      (𝓝 (Real.exp (-0))) :=
    (Real.continuous_exp.tendsto _).comp L_tendsto_top.neg
  have := hq.mul he
  simp only [add_zero, neg_zero, Real.exp_zero, mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  unfold F
  congr 1
  field_simp
  ring

end AlphaAuxE5F6

open RevShareCoord.Wholesale in
theorem solution (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
    (((1 - c) / (1 + α)) ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (supplierProfit (deriv (alphaRevenue α)) c) (Set.Icc 0 1)
        (((1 - c) / (1 + α)) ^ (1 / α)) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (supplierProfit (deriv (alphaRevenue α)) c) (Set.Icc 0 1) q →
          q = ((1 - c) / (1 + α)) ^ (1 / α)) ∧
    ((1 - c) ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (chainProfit (alphaRevenue α) c) (Set.Icc 0 1) ((1 - c) ^ (1 / α)) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (chainProfit (alphaRevenue α) c) (Set.Icc 0 1) q → q = (1 - c) ^ (1 / α)) ∧
    profitShare (alphaRevenue α) (deriv (alphaRevenue α)) c (((1 - c) / (1 + α)) ^ (1 / α)) =
      (1 + α) / (2 + α) ∧
    alphaEfficiency α c = (2 + α) / (1 + α) ^ ((1 + α) / α) ∧
    StrictMonoOn (fun a : ℝ => alphaEfficiency a c) (Set.Ioi 0) ∧
    Filter.Tendsto (fun a : ℝ => alphaEfficiency a c) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 / Real.exp 1)) ∧
    Filter.Tendsto (fun a : ℝ => alphaEfficiency a c) Filter.atTop (nhds 1) := by
  refine ⟨AlphaAuxE5F6.supplier_part α c hα hc0 hc1, AlphaAuxE5F6.chain_part α c hα hc0 hc1,
    AlphaAuxE5F6.share_part α c hα hc0 hc1, AlphaAuxE5F6.eff_closed α c hα hc0 hc1, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only
    rw [AlphaAuxE5F6.eff_eq_F x c hx hc0 hc1, AlphaAuxE5F6.eff_eq_F y c hy hc0 hc1]
    exact AlphaAuxE5F6.F_strictMono hx hy hxy
  · refine AlphaAuxE5F6.F_tendsto_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (AlphaAuxE5F6.eff_eq_F a c ha hc0 hc1).symm
  · refine AlphaAuxE5F6.F_tendsto_top.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
    exact (AlphaAuxE5F6.eff_eq_F a c ha hc0 hc1).symm
