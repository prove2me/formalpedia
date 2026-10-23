-- Prove2me | solution 1 for SPPRevenue.SingleUnit.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:53:04.37949+00:00
-- url     : https://prove2.me/submissions/24440780-878b-4aa1-ba28-637ebfb2bec2

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

section

open Real

namespace SPPNum

/-- polynomial lower bound for 1 - exp(-u) on [0,1]. -/
noncomputable def Lpoly (u : ℝ) : ℝ :=
  u - u^2/2 + u^3/6 - u^4/24 + u^5/120 - u^6/720 + u^7/5040 - u^8 * (9/322560)

lemma one_sub_exp_ge (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Lpoly u ≤ 1 - Real.exp (-u) := by
  have hx : |(-u)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound hx (n := 8) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  have h' := (abs_le.1 h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  unfold Lpoly
  norm_num at h' ⊢
  nlinarith [h']

/-- antiderivative of Lpoly (1/τ). -/
noncomputable def Fanti (τ : ℝ) : ℝ :=
  Real.log τ + (1/2) * (τ⁻¹)^1 - (1/12) * (τ⁻¹)^2 + (1/72) * (τ⁻¹)^3 - (1/480) * (τ⁻¹)^4
    + (1/3600) * (τ⁻¹)^5 - (1/30240) * (τ⁻¹)^6 + (9/2257920) * (τ⁻¹)^7

lemma hasDerivAt_Fanti (τ : ℝ) (hτ : τ ≠ 0) : HasDerivAt Fanti (Lpoly (1/τ)) τ := by
  have hi := hasDerivAt_inv hτ
  have h := (((((((((Real.hasDerivAt_log hτ).add ((hi.pow 1).const_mul (1/2 : ℝ))).sub
    ((hi.pow 2).const_mul (1/12 : ℝ))).add ((hi.pow 3).const_mul (1/72 : ℝ))).sub
    ((hi.pow 4).const_mul (1/480 : ℝ))).add ((hi.pow 5).const_mul (1/3600 : ℝ))).sub
    ((hi.pow 6).const_mul (1/30240 : ℝ))).add ((hi.pow 7).const_mul (9/2257920 : ℝ))))
  refine h.congr_deriv ?_
  unfold Lpoly
  simp only [one_div, ← inv_pow]
  push_cast
  ring

end SPPNum

namespace SPPNum

lemma exp_negc_bounds :
    (0.5896064 : ℝ) ≤ Real.exp (-(5283/10000)) ∧ Real.exp (-(5283/10000)) ≤ (0.5896065 : ℝ) := by
  have hx : |(-(5283/10000 : ℝ))| ≤ 1 := by norm_num [abs_of_nonneg]
  have h := Real.exp_bound hx (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h' := abs_le.1 h
  norm_num at h'
  constructor <;> linarith [h'.1, h'.2]

end SPPNum

namespace SPPNum

lemma integral_lower_bound :
    Real.exp (-1) ≤ ∫ τ in (1:ℝ)..Real.exp (5283/10000), (1 - Real.exp (-(1 / τ))) := by
  set T := Real.exp (5283/10000) with hTdef
  have hT1 : 1 ≤ T := Real.one_le_exp (by norm_num)
  have hne : ∀ x ∈ Set.uIcc 1 T, x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le hT1] at hx; linarith [hx.1]
  have hintL : IntervalIntegrable (fun τ => Lpoly (1 / τ)) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by unfold Lpoly; fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hintf : IntervalIntegrable (fun τ => 1 - Real.exp (-(1 / τ))) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hmono : ∫ τ in (1:ℝ)..T, Lpoly (1 / τ) ≤ ∫ τ in (1:ℝ)..T, (1 - Real.exp (-(1 / τ))) := by
    refine intervalIntegral.integral_mono_on hT1 hintL hintf fun x hx => ?_
    have hx1 : 1 ≤ x := hx.1
    exact one_sub_exp_ge (1 / x) (by positivity) (by rw [div_le_one (by linarith)]; exact hx1)
  have hftc : ∫ τ in (1:ℝ)..T, Lpoly (1 / τ) = Fanti T - Fanti 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_Fanti x (hne x hx)) hintL
  refine le_trans ?_ (hftc ▸ hmono)
  have hTinv : T⁻¹ = Real.exp (-(5283/10000)) := by rw [hTdef, Real.exp_neg]
  have hlogT : Real.log T = 5283/10000 := by rw [hTdef, Real.log_exp]
  obtain ⟨hlo, hhi⟩ := exp_negc_bounds
  set y := Real.exp (-(5283/10000 : ℝ))
  have hy0 : (0:ℝ) ≤ 0.5896064 := by norm_num
  unfold Fanti
  rw [hTinv, hlogT, Real.log_one, inv_one]
  have e1 := Real.exp_neg_one_lt_d9
  have l2 := pow_le_pow_left₀ hy0 hlo 2
  have l3 := pow_le_pow_left₀ hy0 hlo 3
  have l4 := pow_le_pow_left₀ hy0 hlo 4
  have l5 := pow_le_pow_left₀ hy0 hlo 5
  have l6 := pow_le_pow_left₀ hy0 hlo 6
  have l7 := pow_le_pow_left₀ hy0 hlo 7
  have hy0' : 0 ≤ y := Real.exp_nonneg _
  have u2 := pow_le_pow_left₀ hy0' hhi 2
  have u4 := pow_le_pow_left₀ hy0' hhi 4
  have u6 := pow_le_pow_left₀ hy0' hhi 6
  norm_num at l2 l3 l4 l5 l6 l7 u2 u4 u6 e1 ⊢
  linarith

end SPPNum

end

section

open Real MeasureTheory Set
open scoped ENNReal

namespace SPPNum

noncomputable def cT : ℝ := Real.exp (5283/10000)
noncomputable def aT : ℝ := Real.exp (-(5283/10000))
noncomputable def fE (x : ℝ) : ℝ := 1 - Real.exp (-x)
noncomputable def lam : ℝ := aT / fE aT
noncomputable def phi (y : ℝ) : ℝ := y - lam * fE y
noncomputable def Gfun (B σ : ℝ) : ℝ :=
  if σ ≤ B then phi 1 else if σ ≤ B * cT then phi (B / σ) else 0

lemma fE_pos {x : ℝ} (hx : 0 < x) : 0 < fE x := by
  unfold fE; have := Real.exp_lt_one_iff.2 (show -x < 0 by linarith); linarith

lemma aT_pos : 0 < aT := Real.exp_pos _
lemma aT_lt_one : aT < 1 := Real.exp_lt_one_iff.2 (by norm_num)
lemma cT_pos : 0 < cT := Real.exp_pos _
lemma aT_mul_cT : aT * cT = 1 := by
  unfold aT cT; rw [← Real.exp_add]; norm_num

lemma lam_nonneg : 0 ≤ lam := div_nonneg aT_pos.le (fE_pos aT_pos).le

lemma phi_aT : phi aT = 0 := by
  unfold phi lam; have := (fE_pos aT_pos).ne'; field_simp; ring

/-- concavity of `fE` with `fE 0 = 0`. -/
lemma conc (s y : ℝ) (hs0 : 0 ≤ s) (hsy : s ≤ y) (hy : 0 < y) : s * fE y ≤ y * fE s := by
  have hθ0 : 0 ≤ s / y := div_nonneg hs0 hy.le
  have hθ1 : s / y ≤ 1 := (div_le_one hy).2 hsy
  have h := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ (-y)) (sub_nonneg.2 hθ1) hθ0
    (by ring : (1 - s / y) + s / y = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : s / y * -y = -s := by field_simp
  rw [e] at h
  unfold fE
  have h2 : y * Real.exp (-s) ≤ y * (1 - s / y + s / y * Real.exp (-y)) :=
    mul_le_mul_of_nonneg_left h hy.le
  have e2 : y * (1 - s / y + s / y * Real.exp (-y)) = y - s + s * Real.exp (-y) := by
    field_simp
  linarith

lemma phi_le (s y : ℝ) (hs0 : 0 ≤ s) (hsy : s ≤ y) (hy : 0 < y) : phi s ≤ (s / y) * phi y := by
  have h := conc s y hs0 hsy hy
  unfold phi
  have hl := lam_nonneg
  have : lam * (s * fE y) ≤ lam * (y * fE s) := mul_le_mul_of_nonneg_left h hl
  have e : s / y * (y - lam * fE y) = s - lam * (s * fE y) / y := by field_simp
  rw [e]
  have : lam * (s * fE y) / y ≤ lam * fE s := by
    rw [div_le_iff₀ hy]; linarith
  linarith

lemma phi_nonneg {y : ℝ} (hy : aT ≤ y) : 0 ≤ phi y := by
  have hy0 : 0 < y := lt_of_lt_of_le aT_pos hy
  have h := phi_le aT y aT_pos.le hy hy0
  rw [phi_aT] at h
  have : 0 < aT / y := div_pos aT_pos hy0
  by_contra hc; push Not at hc
  nlinarith

lemma pointwise (B σ s : ℝ) (hB : 0 < B) (hσ : 0 < σ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsB : σ * s ≤ B) : s ≤ lam * fE s + Gfun B σ := by
  have key : s - lam * fE s ≤ Gfun B σ := by
    change phi s ≤ _
    unfold Gfun
    split_ifs with h1 h2
    · have h := phi_le s 1 hs0 hs1 one_pos
      have := phi_nonneg aT_lt_one.le
      rw [div_one] at h
      nlinarith
    · have hy0 : 0 < B / σ := div_pos hB hσ
      have hsy : s ≤ B / σ := by rw [le_div_iff₀ hσ]; linarith
      have hya : aT ≤ B / σ := by
        rw [le_div_iff₀ hσ]
        have := aT_mul_cT
        nlinarith [aT_pos]
      have h := phi_le s (B / σ) hs0 hsy hy0
      have hn := phi_nonneg hya
      have : s / (B / σ) ≤ 1 := (div_le_one hy0).2 hsy
      nlinarith [div_nonneg hs0 hy0.le]
    · have hsa : s ≤ aT := by
        push Not at h2
        have : σ * s ≤ σ * aT := by
          have := aT_mul_cT
          nlinarith [aT_pos]
        exact le_of_mul_le_mul_left this hσ
      have h := phi_le s aT hs0 hsa aT_pos
      rw [phi_aT, mul_zero] at h
      exact h
  linarith

lemma Gfun_measurable (B : ℝ) : Measurable (Gfun B) := by
  unfold Gfun
  refine Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic ?_ measurable_const)
  unfold phi fE
  fun_prop

end SPPNum

namespace SPPNum

lemma cT_ge_one : 1 ≤ cT := Real.one_le_exp (by norm_num)

lemma int_phi_inv :
    ∫ τ in (1:ℝ)..cT, phi (1 / τ) =
      5283/10000 - lam * ∫ τ in (1:ℝ)..cT, (1 - Real.exp (-(1 / τ))) := by
  have hne : ∀ x ∈ Set.uIcc 1 cT, x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le cT_ge_one] at hx; linarith [hx.1]
  have h0 : (0:ℝ) ∉ Set.uIcc 1 cT := fun h => hne 0 h rfl
  have hint1 : IntervalIntegrable (fun τ : ℝ => 1 / τ) volume 1 cT := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hintf : IntervalIntegrable (fun τ => 1 - Real.exp (-(1 / τ))) volume 1 cT := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  unfold phi fE
  rw [intervalIntegral.integral_sub hint1 (hintf.const_mul lam), intervalIntegral.integral_const_mul,
    integral_one_div h0, div_one]
  unfold cT; rw [Real.log_exp]

lemma J_eq (B : ℝ) (hB : 0 < B) :
    ∫ σ in B..B * cT, phi (B / σ) =
      B * (5283/10000 - lam * ∫ τ in (1:ℝ)..cT, (1 - Real.exp (-(1 / τ)))) := by
  have h := intervalIntegral.integral_comp_mul_left (a := 1) (b := cT)
    (fun σ => phi (B / σ)) hB.ne'
  rw [mul_one] at h
  rw [← int_phi_inv]
  have hc : ∫ x in (1:ℝ)..cT, phi (B / (B * x)) = ∫ x in (1:ℝ)..cT, phi (1 / x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le cT_ge_one] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    change phi (B / (B * x)) = phi (1 / x)
    congr 1
    field_simp
  rw [hc] at h
  rw [h, smul_eq_mul]
  field_simp

end SPPNum

namespace SPPNum

lemma fE_pos' {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) := by
  have := Real.exp_le_one_iff.2 (show -x ≤ 0 by linarith); linarith

lemma phi_div_nonneg (B σ : ℝ) (hB : 0 < B) (hσ0 : 0 < σ) (hσ : σ ≤ B * cT) :
    0 ≤ phi (B / σ) := by
  apply phi_nonneg
  rw [le_div_iff₀ hσ0]
  have := aT_mul_cT
  nlinarith [aT_pos]

lemma Gfun_nonneg (B σ : ℝ) (hB : 0 < B) : 0 ≤ Gfun B σ := by
  unfold Gfun
  split_ifs with h1 h2
  · exact phi_nonneg aT_lt_one.le
  · exact phi_div_nonneg B σ hB (lt_trans hB (lt_of_not_ge h1)) h2
  · exact le_refl _

lemma J_nonneg (B : ℝ) (hB : 0 < B) :
    0 ≤ B * (5283/10000 - lam * ∫ τ in (1:ℝ)..cT, (1 - Real.exp (-(1 / τ)))) := by
  rw [← J_eq B hB, intervalIntegral.integral_of_le (le_mul_of_one_le_right hB.le cT_ge_one)]
  exact setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
    phi_div_nonneg B σ hB (lt_trans hB hσ.1) hσ.2

lemma lint_G (B : ℝ) (hB : 0 < B) :
    ∫⁻ σ in Ioi 0, ENNReal.ofReal (Gfun B σ) ≤
      ENNReal.ofReal (B * phi 1 + B * (5283/10000 - lam * ∫ τ in (1:ℝ)..cT,
        (1 - Real.exp (-(1 / τ))))) := by
  have hBT : B ≤ B * cT := le_mul_of_one_le_right hB.le cT_ge_one
  have hsub : Ioi (0:ℝ) ⊆ (Ioc 0 B ∪ Ioc B (B * cT)) ∪ Ioi (B * cT) := by
    intro x hx
    simp only [mem_union, mem_Ioc, mem_Ioi] at hx ⊢
    by_cases h1 : x ≤ B
    · exact Or.inl (Or.inl ⟨hx, h1⟩)
    · by_cases h2 : x ≤ B * cT
      · exact Or.inl (Or.inr ⟨lt_of_not_ge h1, h2⟩)
      · exact Or.inr (lt_of_not_ge h2)
  have hp1 : 0 ≤ phi 1 := phi_nonneg aT_lt_one.le
  -- piece 1
  have e1 : ∫⁻ σ in Ioc 0 B, ENNReal.ofReal (Gfun B σ) = ENNReal.ofReal (B * phi 1) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal (phi 1))]
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ← ENNReal.ofReal_mul hp1, mul_comm]
    · intro x hx; simp only [Gfun, if_pos hx.2]
  -- piece 2
  have hcont : ContinuousOn (fun σ => phi (B / σ)) (Icc B (B * cT)) := by
    intro x hx
    have : x ≠ 0 := by linarith [hx.1]
    exact (by unfold phi fE; fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hnn : ∀ σ ∈ Ioc B (B * cT), 0 ≤ phi (B / σ) := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_trans hB hσ.1
    apply phi_nonneg
    rw [le_div_iff₀ hσ0]
    have := aT_mul_cT
    have := hσ.2
    nlinarith [aT_pos]
  have e2 : ∫⁻ σ in Ioc B (B * cT), ENNReal.ofReal (Gfun B σ) =
      ENNReal.ofReal (∫ σ in B..B * cT, phi (B / σ)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun σ => ENNReal.ofReal (phi (B / σ)))]
    · rw [intervalIntegral.integral_of_le hBT, ofReal_integral_eq_lintegral_ofReal]
      · exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      · exact ae_restrict_of_forall_mem measurableSet_Ioc hnn
    · intro x hx; simp only [Gfun, if_neg (not_le.2 hx.1), if_pos hx.2]
  have e3 : ∫⁻ σ in Ioi (B * cT), ENNReal.ofReal (Gfun B σ) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)]
    · simp
    · intro x hx
      have hx' : B * cT < x := hx
      simp only [Gfun, if_neg (not_le.2 (lt_of_le_of_lt hBT hx')), if_neg (not_le.2 hx'),
        ENNReal.ofReal_zero]
  calc ∫⁻ σ in Ioi 0, ENNReal.ofReal (Gfun B σ)
      ≤ ∫⁻ σ in (Ioc 0 B ∪ Ioc B (B * cT)) ∪ Ioi (B * cT), ENNReal.ofReal (Gfun B σ) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ σ in Ioc 0 B, ENNReal.ofReal (Gfun B σ)) +
          (∫⁻ σ in Ioc B (B * cT), ENNReal.ofReal (Gfun B σ)) +
          ∫⁻ σ in Ioi (B * cT), ENNReal.ofReal (Gfun B σ) := by
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        exact lintegral_union_le _ _ _
    _ = ENNReal.ofReal (B * phi 1) + ENNReal.ofReal (∫ σ in B..B * cT, phi (B / σ)) := by
        rw [e1, e2, e3, add_zero]
    _ = _ := by
        rw [← J_eq B hB, ← ENNReal.ofReal_add (mul_nonneg hB.le hp1)]
        rw [J_eq B hB]
        exact J_nonneg B hB

/-- The factor-revealing bound, in unnormalized form. -/
theorem fr_bound (S : ℝ → ℝ≥0∞) (B : ℝ) (hB : 0 < B) (h1 : ∀ σ, S σ ≤ 1)
    (h2 : ∀ σ, 0 < σ → ENNReal.ofReal σ * S σ ≤ ENNReal.ofReal B)
    (h3 : ∫⁻ σ in Ioi 0, ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) ≤ ENNReal.ofReal B) :
    ∫⁻ σ in Ioi 0, S σ ≤ ENNReal.ofReal (B * (1 + 5283/10000)) := by
  have hpt : ∀ σ ∈ Ioi (0:ℝ), S σ ≤ ENNReal.ofReal lam *
      ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) + ENNReal.ofReal (Gfun B σ) := by
    intro σ hσ
    have hσ0 : 0 < σ := hσ
    have hfin : S σ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (h1 σ)
    set s := (S σ).toReal with hs
    have hS : S σ = ENNReal.ofReal s := (ENNReal.ofReal_toReal hfin).symm
    have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
    have hs1 : s ≤ 1 := by
      have := h1 σ; rw [hS] at this; exact (ENNReal.ofReal_le_one).1 this
    have hsB : σ * s ≤ B := by
      have := h2 σ hσ0
      rw [hS, ← ENNReal.ofReal_mul hσ0.le, ENNReal.ofReal_le_ofReal_iff hB.le] at this
      exact this
    have hp := pointwise B σ s hB hσ0 hs0 hs1 hsB
    rw [hS, ← ENNReal.ofReal_mul lam_nonneg]
    have hf0 : 0 ≤ lam * (1 - Real.exp (-s)) :=
      mul_nonneg lam_nonneg (fE_pos' hs0)
    rw [← ENNReal.ofReal_add hf0 (Gfun_nonneg B σ hB)]
    exact ENNReal.ofReal_le_ofReal hp
  calc ∫⁻ σ in Ioi 0, S σ
      ≤ ∫⁻ σ in Ioi 0, (ENNReal.ofReal lam *
          ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) + ENNReal.ofReal (Gfun B σ)) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    _ = ENNReal.ofReal lam * (∫⁻ σ in Ioi 0, ENNReal.ofReal (1 - Real.exp (-(S σ).toReal))) +
          ∫⁻ σ in Ioi 0, ENNReal.ofReal (Gfun B σ) := by
        rw [lintegral_add_right _ ((Gfun_measurable B).ennreal_ofReal),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal lam * ENNReal.ofReal B +
          ENNReal.ofReal (B * phi 1 + B * (5283/10000 - lam * ∫ τ in (1:ℝ)..cT,
            (1 - Real.exp (-(1 / τ))))) := by
        gcongr
        exact lint_G B hB
    _ = ENNReal.ofReal (lam * B + (B * phi 1 + B * (5283/10000 - lam * ∫ τ in (1:ℝ)..cT,
            (1 - Real.exp (-(1 / τ)))))) := by
        rw [← ENNReal.ofReal_mul lam_nonneg, ENNReal.ofReal_add (mul_nonneg lam_nonneg hB.le)]
        exact add_nonneg (mul_nonneg hB.le (phi_nonneg aT_lt_one.le)) (J_nonneg B hB)
    _ ≤ ENNReal.ofReal (B * (1 + 5283/10000)) := by
        apply ENNReal.ofReal_le_ofReal
        have hI := integral_lower_bound
        have hl := lam_nonneg
        unfold phi fE
        change Real.exp (-1) ≤ ∫ τ in (1:ℝ)..cT, (1 - Real.exp (-(1 / τ))) at hI
        nlinarith [mul_nonneg hl hB.le]

end SPPNum

end

section

open MeasureTheory Set
open scoped ENNReal

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

lemma sStarI_antitone (i : Fin n) : Antitone (sStarI μ t i) := fun a b hab =>
  measure_mono fun _ hv => ⟨hv.1, le_trans hab hv.2⟩

lemma sStar_antitone : Antitone (sStar μ t) := by
  intro a b hab
  exact Finset.sum_le_sum fun i _ => sStarI_antitone μ t i hab

lemma opt_eq (hm : ∀ i, Measurable (t i)) (hnn : ∀ i v, 0 ≤ t i v) :
    optRev μ t = ∫⁻ τ in Ioi 0, sStar μ t τ := by
  unfold optRev sStar
  have hmeasA : ∀ i, MeasurableSet {v : Fin n → ℝ | t i v ≤ v i} := fun i =>
    measurableSet_le (hm i) (measurable_pi_apply i)
  rw [lintegral_finsetSum _ (fun i _ =>
    Measurable.ite (hmeasA i) (hm i).ennreal_ofReal measurable_const)]
  rw [lintegral_finsetSum' _ (fun i _ => (sStarI_antitone μ t i).measurable.aemeasurable)]
  refine Finset.sum_congr rfl fun i _ => ?_
  set g : (Fin n → ℝ) → ℝ := fun v => if t i v ≤ v i then t i v else 0 with hg
  have hfun : (fun v => if t i v ≤ v i then ENNReal.ofReal (t i v) else 0) =
      fun v => ENNReal.ofReal (g v) := by
    funext v; simp only [hg]; split_ifs <;> simp
  have hgm : Measurable g := Measurable.ite (hmeasA i) (hm i) measurable_const
  have hg0 : ∀ v, 0 ≤ g v := fun v => by simp only [hg]; split_ifs; exacts [hnn i v, le_rfl]
  rw [hfun, lintegral_eq_lintegral_meas_le _ (ae_of_all _ hg0) hgm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  have hτ0 : 0 < τ := hτ
  unfold sStarI
  congr 1
  ext v
  simp only [hg, mem_setOf_eq]
  split_ifs with h
  · exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · exact ⟨fun h' => absurd h' (not_le.2 hτ0), fun h' => absurd h'.1 h⟩

lemma measA (ht : IsThresholdMech μ t) (τ : ℝ) (i : Fin n) :
    MeasurableSet {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v} :=
  (measurableSet_le (ht.measurable i) (measurable_pi_apply i)).inter
    (measurableSet_le measurable_const (ht.measurable i))

lemma sStar_eq_union (ht : IsThresholdMech μ t) (τ : ℝ) :
    sStar μ t τ = Measure.pi μ (⋃ i ∈ (Finset.univ : Finset (Fin n)),
      {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v}) := by
  unfold sStar sStarI
  rw [measure_biUnion_finset₀]
  · intro i _ j _ hij
    refine measure_mono_null ?_ (ae_iff.1 ht.single_unit)
    intro v hv
    simp only [mem_setOf_eq, not_forall]
    exact ⟨i, j, hv.1.1, hv.2.1, hij⟩
  · exact fun i _ => (measA μ t ht τ i).nullMeasurableSet

lemma sStar_le_one (ht : IsThresholdMech μ t) (τ : ℝ) : sStar μ t τ ≤ 1 := by
  rw [sStar_eq_union μ t ht]; exact prob_le_one

lemma up_bound (ht : IsThresholdMech μ t) (τ : ℝ) :
    ENNReal.ofReal τ * sStar μ t τ ≤ sppRev μ (fun _ => τ) := by
  rw [sStar_eq_union μ t ht]
  set U := ⋃ i ∈ (Finset.univ : Finset (Fin n)), {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v}
  have hU : MeasurableSet U := Finset.measurableSet_biUnion _ fun i _ => measA μ t ht τ i
  rw [← lintegral_indicator_const hU]
  unfold sppRev
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ U
  · rw [indicator_of_mem hv]
    simp only [U, mem_iUnion, Finset.mem_univ, exists_true_left, mem_setOf_eq] at hv
    obtain ⟨i, h1, h2⟩ := hv
    unfold sppRevAt
    exact Finset.le_sup (f := fun i => ENNReal.ofReal ((fun _ => τ) i))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_trans h2 h1⟩)
  · rw [indicator_of_notMem hv]; exact zero_le

lemma mp_le (ht : IsThresholdMech μ t) (X : ℝ≥0∞)
    (h : ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → sppRev μ p ≤ X) : mpRev μ t ≤ X := by
  unfold mpRev resampleLaw
  refine (lintegral_prod_le _).trans ?_
  calc ∫⁻ W, ∫⁻ v, sppRevAt (fun i => t i ((W, v).1 i)) (W, v).2 ∂(Measure.pi μ)
        ∂(Measure.pi fun _ : Fin n => Measure.pi μ)
      ≤ ∫⁻ _W, X ∂(Measure.pi fun _ : Fin n => Measure.pi μ) :=
        lintegral_mono fun W => h (fun i => t i (W i)) fun i => ht.nonneg i _
    _ = X := by rw [lintegral_const, measure_univ, mul_one]

end SPPAux

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

instance resampleLaw_prob : IsProbabilityMeasure (resampleLaw μ) := by
  unfold resampleLaw; infer_instance

lemma sppRevAt_ne_top (p v : Fin n → ℝ) : sppRevAt p v ≠ ⊤ := by
  unfold sppRevAt
  exact ((Finset.sup_lt_iff (a := (⊤ : ℝ≥0∞)) bot_lt_top).2
    fun i _ => ENNReal.ofReal_lt_top).ne

lemma mp_ge (ht : IsThresholdMech μ t) :
    ∫⁻ τ in Ioi 0, mSell μ t τ ≤ mpRev μ t := by
  set E : Set (((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ) :=
    {z | ∃ i, t i (z.1.1 i) ≤ z.1.2 i ∧ z.2 ≤ t i (z.1.1 i)} with hEdef
  have hE : MeasurableSet E := by
    have : E = ⋃ i, ({z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ | t i (z.1.1 i) ≤ z.1.2 i} ∩
        {z | z.2 ≤ t i (z.1.1 i)}) := by
      ext z; simp [hEdef]
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    have m1 : Measurable fun z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ => t i (z.1.1 i) :=
      (ht.measurable i).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
    have m2 : Measurable fun z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ => z.1.2 i :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    exact (measurableSet_le m1 m2).inter (measurableSet_le measurable_snd m1)
  have hmS : ∀ τ, mSell μ t τ = ∫⁻ x, E.indicator 1 (x, τ) ∂(resampleLaw μ) := by
    intro τ
    have hs : MeasurableSet {x : (Fin n → Fin n → ℝ) × (Fin n → ℝ) | (x, τ) ∈ E} :=
      measurable_prodMk_right hE
    have := lintegral_indicator_one (μ := resampleLaw μ) hs
    unfold mSell
    exact this.symm
  simp_rw [hmS]
  rw [lintegral_lintegral_swap]
  · unfold mpRev
    refine lintegral_mono fun x => ?_
    set F := sppRevAt (fun i => t i (x.1 i)) x.2 with hF
    have hFtop : F ≠ ⊤ := sppRevAt_ne_top _ _
    have hle : ∀ τ, E.indicator 1 (x, τ) ≤ (Iic F.toReal).indicator (1 : ℝ → ℝ≥0∞) τ := by
      intro τ
      by_cases hxτ : (x, τ) ∈ E
      · rw [indicator_of_mem hxτ]
        obtain ⟨i, h1, h2⟩ := hxτ
        have hi : ENNReal.ofReal (t i (x.1 i)) ≤ F := by
          rw [hF]; unfold sppRevAt
          exact Finset.le_sup (f := fun j => ENNReal.ofReal ((fun j => t j (x.1 j)) j))
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
        have : τ ≤ F.toReal := le_trans h2 ((ENNReal.ofReal_le_iff_le_toReal hFtop).1 hi)
        rw [indicator_of_mem (show τ ∈ Iic F.toReal from this)]
        simp
      · rw [indicator_of_notMem hxτ]; exact zero_le
    calc ∫⁻ τ in Ioi 0, E.indicator 1 (x, τ)
        ≤ ∫⁻ τ in Ioi 0, (Iic F.toReal).indicator 1 τ := lintegral_mono hle
      _ = volume (Iic F.toReal ∩ Ioi 0) := by
        rw [lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
      _ ≤ volume (Ioc 0 F.toReal) := by
        apply measure_mono; intro y hy; exact ⟨hy.2, hy.1⟩
      _ = F := by rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal hFtop]
  · exact ((measurable_one.indicator hE).comp measurable_swap).aemeasurable

end SPPAux

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

lemma mp_update (i : Fin n) :
    MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) where
  measurable := measurable_update'
  map_eq := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
    have hpre : (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.pi univ s) =
        (Set.pi univ (Function.update s i univ)) ×ˢ (s i) := by
      ext ⟨w, a⟩
      simp only [mem_preimage, mem_univ_pi, mem_prod]
      constructor
      · intro h
        refine ⟨fun j => ?_, ?_⟩
        · by_cases hj : j = i
          · subst hj; simp
          · have := h j; rw [Function.update_of_ne hj] at this
            rw [Function.update_of_ne hj]; exact this
        · have := h i; rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact h2
        · rw [Function.update_of_ne hj]; have := h1 j; rwa [Function.update_of_ne hj] at this
    rw [hpre, Measure.prod_prod, Measure.pi_pi]
    rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => μ j (s j))]
    rw [Function.update_self, measure_univ, one_mul, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := by simpa using hj
    rw [Function.update_of_ne this]

lemma prod_set_eq (ht : IsThresholdMech μ t) (τ : ℝ) (i : Fin n) :
    ((Measure.pi μ).prod (μ i)) {p : (Fin n → ℝ) × ℝ | t i p.1 ≤ p.2 ∧ τ ≤ t i p.1} =
      sStarI μ t i τ := by
  have hpre : (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹'
      {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v} =
      {p : (Fin n → ℝ) × ℝ | t i p.1 ≤ p.2 ∧ τ ≤ t i p.1} := by
    ext ⟨w, a⟩
    have h : t i (Function.update w i a) = t i w :=
      ht.indep_own i _ _ fun j hj => Function.update_of_ne hj _ _
    simp only [mem_preimage, mem_setOf_eq, h, Function.update_self]
  rw [← hpre, (mp_update μ i).measure_preimage (measA μ t ht τ i).nullMeasurableSet]
  rfl

lemma one_sub_le_exp (s : ℝ≥0∞) (hs : s ≤ 1) :
    1 - s ≤ ENNReal.ofReal (Real.exp (-s.toReal)) := by
  have hfin : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
  have : 1 - s = ENNReal.ofReal (1 - s.toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal hfin]
  rw [this]
  apply ENNReal.ofReal_le_ofReal
  have := Real.add_one_le_exp (-s.toReal)
  linarith

lemma mSell_ge (ht : IsThresholdMech μ t) (τ : ℝ) :
    ENNReal.ofReal (1 - Real.exp (-(sStar μ t τ).toReal)) ≤ mSell μ t τ := by
  set A : Fin n → Set ((Fin n → ℝ) × ℝ) :=
    fun i => {p : (Fin n → ℝ) × ℝ | t i p.1 ≤ p.2 ∧ τ ≤ t i p.1} with hAdef
  have hA : ∀ i, MeasurableSet (A i) := fun i =>
    (measurableSet_le ((ht.measurable i).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_const ((ht.measurable i).comp measurable_fst))
  set X : Set ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) :=
    {x | ∃ i, t i (x.1 i) ≤ x.2 i ∧ τ ≤ t i (x.1 i)} with hXdef
  have hX : MeasurableSet X := by
    have : X = ⋃ i, ({x : (Fin n → Fin n → ℝ) × (Fin n → ℝ) | t i (x.1 i) ≤ x.2 i} ∩
        {x | τ ≤ t i (x.1 i)}) := by
      ext z; simp [hXdef]
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    have m1 : Measurable fun z : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => t i (z.1 i) :=
      (ht.measurable i).comp ((measurable_pi_apply i).comp measurable_fst)
    have m2 : Measurable fun z : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => z.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact (measurableSet_le m1 m2).inter (measurableSet_le measurable_const m1)
  -- measure of the complement
  have hmp := measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)
    (fun _ => Measure.pi μ) μ
  have hcompl : resampleLaw μ Xᶜ = ∏ i, ((Measure.pi μ).prod (μ i)) (A i)ᶜ := by
    unfold resampleLaw
    rw [← hmp.measure_preimage hX.compl.nullMeasurableSet]
    have : (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)) ⁻¹' Xᶜ =
        Set.pi univ (fun i => (A i)ᶜ) := by
      ext f
      simp [hXdef, hAdef, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    rw [this, Measure.pi_pi]
  have hprod : ∏ i, ((Measure.pi μ).prod (μ i)) (A i)ᶜ =
      ∏ i, (1 - sStarI μ t i τ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [prob_compl_eq_one_sub (hA i), hAdef, prod_set_eq μ t ht τ i]
  have hsI1 : ∀ i, sStarI μ t i τ ≤ 1 := fun i => prob_le_one
  have hfinI : ∀ i, sStarI μ t i τ ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hsI1 i)
  have hbound : ∏ i, (1 - sStarI μ t i τ) ≤ ENNReal.ofReal (Real.exp (-(sStar μ t τ).toReal)) := by
    unfold sStar
    rw [ENNReal.toReal_sum fun i _ => hfinI i, ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
    exact Finset.prod_le_prod' fun i _ => one_sub_le_exp _ (hsI1 i)
  have hm : mSell μ t τ = 1 - resampleLaw μ Xᶜ := by
    rw [prob_compl_eq_one_sub hX, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rfl
  rw [hm, hcompl, hprod, ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hbound 1

end SPPAux

end


open MeasureTheory Set
open scoped ENNReal
open SPPRevenue.SingleUnit

theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) (hfin : optRev μ t ≠ ⊤) :
    ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧
      ENNReal.ofReal (6543 / 10000) * optRev μ t ≤ sppRev μ p := by
  by_contra hcon
  push Not at hcon
  have hO0 : optRev μ t ≠ 0 := by
    intro h0
    have := hcon (fun _ => 0) (fun _ => le_rfl)
    rw [h0, mul_zero] at this
    exact ENNReal.not_lt_zero this
  have hOpos : 0 < (optRev μ t).toReal := ENNReal.toReal_pos hO0 hfin
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 6543 / 10000 * (optRev μ t).toReal := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hBdef]; positivity
  have hBe : ENNReal.ofReal (6543 / 10000) * optRev μ t = ENNReal.ofReal B := by
    rw [hBdef, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfin]
  have hsp : ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → sppRev μ p ≤ ENNReal.ofReal B :=
    fun p hp => (hcon p hp).le.trans_eq hBe
  have h2 : ∀ σ : ℝ, 0 < σ → ENNReal.ofReal σ * sStar μ t σ ≤ ENNReal.ofReal B :=
    fun σ hσ => (SPPAux.up_bound μ t ht σ).trans (hsp _ fun _ => hσ.le)
  have h3 : ∫⁻ σ in Ioi 0, ENNReal.ofReal (1 - Real.exp (-(sStar μ t σ).toReal)) ≤
      ENNReal.ofReal B :=
    (lintegral_mono fun τ => SPPAux.mSell_ge μ t ht τ).trans
      ((SPPAux.mp_ge μ t ht).trans (SPPAux.mp_le μ t ht _ hsp))
  have hfr := SPPNum.fr_bound (sStar μ t) B hB (SPPAux.sStar_le_one μ t ht) h2 h3
  rw [← SPPAux.opt_eq μ t ht.measurable ht.nonneg] at hfr
  have hle : (optRev μ t).toReal ≤ B * (1 + 5283 / 10000) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfr
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  rw [hBdef] at hle
  nlinarith
