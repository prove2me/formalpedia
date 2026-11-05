-- Prove2me | solution 1 for TikhonovHDD.Ergodic.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:09:41.935932+00:00
-- url     : https://prove2.me/submissions/66118fbc-bc46-4dce-b00d-c0581efe0114

import Mathlib
import Definitions.Def_TikhonovHDD_Ergodic_TikhonovCurve
import Definitions.Def_TikhonovHDD_Ergodic_Setting
import Theorems.Thm_TikhonovHDD_Ergodic_eq_46
import Theorems.Thm_TikhonovHDD_Ergodic_tikhonov_curve_tendsto

open Set Filter Topology MeasureTheory

namespace TikhThm42Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma mid_norm_sq (a b : H) :
    ‖(1/2 : ℝ) • a + (1/2 : ℝ) • b‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - ‖a - b‖ ^ 2 / 4 := by
  have h1 : (1/2 : ℝ) • a + (1/2 : ℝ) • b = (1/2 : ℝ) • (a + b) := by
    rw [smul_add]
  rw [h1, norm_smul, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  norm_num
  ring

lemma mid_ineq (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (e : ℝ) (a b : H) :
    g ((1/2 : ℝ) • a + (1/2 : ℝ) • b) + e / 2 * ‖(1/2 : ℝ) • a + (1/2 : ℝ) • b‖ ^ 2 ≤
      ((g a + e / 2 * ‖a‖ ^ 2) + (g b + e / 2 * ‖b‖ ^ 2)) / 2 - e / 8 * ‖a - b‖ ^ 2 := by
  have hc := hconv.2 (mem_univ a) (mem_univ b) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [mid_norm_sq]
  nlinarith

/-- Existence of the Tikhonov point `x_e` for `e > 0`. -/
lemma exists_tikhonov [CompleteSpace H] (g : H → ℝ) (hconv : ConvexOn ℝ univ g)
    (hcont : Continuous g) (hne : (TikhonovHDD.Strong.argminSet g).Nonempty)
    (e : ℝ) (he : 0 < e) : ∃ y, TikhonovHDD.Ergodic.IsTikhonovPoint g e y := by
  obtain ⟨xh, hxh⟩ := hne
  set F : H → ℝ := fun z => g z + e / 2 * ‖z‖ ^ 2 with hF
  have hFlb : ∀ z, g xh ≤ F z := fun z => by
    have := hxh z
    have : 0 ≤ e / 2 * ‖z‖ ^ 2 := by positivity
    simp only [hF]; linarith
  have hbdd : BddBelow (range F) := ⟨g xh, by rintro _ ⟨z, rfl⟩; exact hFlb z⟩
  set m := sInf (range F)
  have hmle : ∀ z, m ≤ F z := fun z => csInf_le hbdd ⟨z, rfl⟩
  have hseq : ∀ n : ℕ, ∃ y, F y < m + 1 / ((n:ℝ) + 1) := by
    intro n
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := exists_lt_of_csInf_lt (range_nonempty F)
      (show m < m + 1 / ((n:ℝ) + 1) by linarith)
    exact ⟨y, hy⟩
  choose y hy using hseq
  have hmono : ∀ N n : ℕ, N ≤ n → 1 / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := by
    intro N n hNn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hNn 1
  have hdist : ∀ n k N : ℕ, N ≤ n → N ≤ k →
      dist (y n) (y k) ≤ Real.sqrt (8 / e * (1 / ((N:ℝ) + 1))) := by
    intro n k N hn hk
    have h1 := mid_ineq g hconv e (y n) (y k)
    have h2 := hmle ((1/2 : ℝ) • y n + (1/2 : ℝ) • y k)
    have h3 := hy n
    have h4 := hy k
    have h5 := hmono N n hn
    have h6 := hmono N k hk
    simp only [hF] at h2 h3 h4
    have hD : ‖y n - y k‖ ^ 2 ≤ 8 / e * (1 / ((N:ℝ) + 1)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ he]
      nlinarith
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hD
  have hb : Tendsto (fun N : ℕ => Real.sqrt (8 / e * (1 / ((N:ℝ) + 1)))) atTop (𝓝 0) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (8 / e)
    rw [mul_zero] at h0
    have := ((Real.continuous_sqrt.tendsto 0).comp h0)
    rw [Real.sqrt_zero] at this
    exact this
  have hcs : CauchySeq y := cauchySeq_of_le_tendsto_0 _ hdist hb
  obtain ⟨y0, hy0⟩ := cauchySeq_tendsto_of_complete hcs
  have hFc : Continuous F := hcont.add (continuous_const.mul (continuous_norm.pow 2))
  have hlim1 : Tendsto (fun n => F (y n)) atTop (𝓝 (F y0)) := (hFc.tendsto y0).comp hy0
  have hlim2 : Tendsto (fun n => F (y n)) atTop (𝓝 m) := by
    have hup : Tendsto (fun n : ℕ => m + 1 / ((n:ℝ) + 1)) atTop (𝓝 (m + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => hmle (y n)) (fun n => (hy n).le)
  have hFy0 : F y0 = m := tendsto_nhds_unique hlim1 hlim2
  refine ⟨y0, fun z => ?_⟩
  have := hmle z
  have h' : F y0 ≤ F z := by rw [hFy0]; exact this
  simpa [hF] using h'

end TikhThm42Aux

open TikhonovHDD.Ergodic TikhThm42Aux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (ht₀ : 0 < t₀) (hα : 0 < α) (hβ : 0 ≤ β)
    (hg : GeneralAssumptionG g) (hε : GeneralAssumptionEps t₀ ε ε')
    (hx : IsSolution g α β ε t₀ u₀ v₀ x xd xdd)
    (hdiv : Tendsto (fun T => ∫ t in t₀..T, ε t / t) atTop atTop)
    (hxstar : TikhonovHDD.Strong.IsMinNormMinimizer g xstar) :
    Tendsto (fun t => (∫ s in t₀..t, ε s / s)⁻¹ * ∫ s in t₀..t, ε s / s * ‖x s - xstar‖ ^ 2)
        atTop (𝓝 0) ∧
      ∀ δ > 0, ∃ᶠ t in atTop, ‖x t - xstar‖ < δ := by
  obtain ⟨hconv, hdiff, -, -, hne⟩ := id hg
  obtain ⟨hεd, -, hεnn, hεanti, hεlim⟩ := id hε
  obtain ⟨hxode, -, -, -⟩ := id hx
  have gcont : Continuous g := hdiff.continuous
  -- the Tikhonov curve
  have hex := exists_tikhonov g hconv gcont hne
  set Xe : ℝ → H := fun e => if h : 0 < e then Classical.choose (hex e h) else 0 with hXedef
  have hXe : ∀ e > 0, IsTikhonovPoint g e (Xe e) := by
    intro e he
    simp only [hXedef, dif_pos he]
    exact Classical.choose_spec (hex e he)
  have hnorm : ∀ e > 0, ‖Xe e‖ ^ 2 ≤ ‖xstar‖ ^ 2 := by
    intro e he
    have h1 := hXe e he xstar
    have h2 := hxstar.1 (Xe e)
    have : e / 2 * ‖Xe e‖ ^ 2 ≤ e / 2 * ‖xstar‖ ^ 2 := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hanti : ∀ a b : ℝ, 0 < b → b ≤ a → ‖Xe a‖ ^ 2 ≤ ‖Xe b‖ ^ 2 := by
    intro a b hb hba
    rcases eq_or_lt_of_le hba with hab | hab
    · rw [hab]
    · have ha : 0 < a := hb.trans hab
      have h1 := hXe a ha (Xe b)
      have h2 := hXe b hb (Xe a)
      by_contra hc
      push Not at hc
      have : 0 < (a - b) * (‖Xe a‖ ^ 2 - ‖Xe b‖ ^ 2) := mul_pos (by linarith) (by linarith)
      nlinarith
  -- continuity facts
  have xcont : ContinuousOn x (Ici t₀) := fun t ht => (hxode t ht).1.continuousWithinAt
  have εcont : ContinuousOn ε (Ici t₀) := fun t ht => (hεd t ht).continuousWithinAt
  have wcont : ContinuousOn (fun s => ε s / s) (Ici t₀) :=
    εcont.div continuousOn_id (fun s hs => ne_of_gt (lt_of_lt_of_le ht₀ hs))
  have hsub : ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b → uIcc a b ⊆ Ici t₀ :=
    fun a b ha hb s hs => le_trans (le_min ha hb) hs.1
  have hII : ∀ f : ℝ → ℝ, ContinuousOn f (Ici t₀) → ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b →
      IntervalIntegrable f volume a b :=
    fun f hf a b ha hb => (hf.mono (hsub a b ha hb)).intervalIntegrable
  have wII := hII _ wcont
  have wnn : ∀ s, t₀ ≤ s → 0 ≤ ε s / s := fun s hs =>
    div_nonneg (hεnn s hs) (ht₀.le.trans hs)
  -- positivity of ε
  have hpos : ∀ s, t₀ ≤ s → 0 < ε s := by
    intro s1 hs1
    by_contra hc
    have hz : ε s1 = 0 := le_antisymm (not_lt.mp hc) (hεnn s1 hs1)
    have hzero : ∀ T, s1 ≤ T → ∫ t in t₀..T, ε t / t = ∫ t in t₀..s1, ε t / t := by
      intro T hT
      rw [← intervalIntegral.integral_add_adjacent_intervals (wII t₀ s1 le_rfl hs1)
        (wII s1 T hs1 (hs1.trans hT))]
      have : ∫ t in s1..T, ε t / t = 0 := by
        have hc0 : ∫ t in s1..T, ε t / t = ∫ t in s1..T, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hT] at ht
          have h1 : ε t ≤ ε s1 := hεanti (show s1 ∈ Ici t₀ from hs1)
            (show t ∈ Ici t₀ from hs1.trans ht.1) ht.1
          have h2 := hεnn t (hs1.trans ht.1)
          have : ε t = 0 := by linarith
          simp [this]
        rw [hc0]; simp
      rw [this, add_zero]
    obtain ⟨T, hT1, hT2⟩ := ((hdiv.eventually_gt_atTop (∫ t in t₀..s1, ε t / t)).and
      (eventually_ge_atTop s1)).exists
    rw [hzero T hT2] at hT1
    exact lt_irrefl _ hT1
  -- the function φ
  set φ : ℝ → ℝ := fun s => ‖xstar‖ ^ 2 - ‖Xe (ε s)‖ ^ 2 with hφ
  have φnn : ∀ s, t₀ ≤ s → 0 ≤ φ s := fun s hs => by
    have := hnorm (ε s) (hpos s hs); simp only [hφ]; linarith
  have φanti : AntitoneOn φ (Ici t₀) := by
    intro s1 hs1 s2 hs2 h12
    have := hanti (ε s1) (ε s2) (hpos s2 hs2) (hεanti hs1 hs2 h12)
    simp only [hφ]; linarith
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hεlim, (eventually_ge_atTop t₀).mono fun s hs => hpos s hs⟩
  have hXlim : Tendsto (fun s => Xe (ε s)) atTop (𝓝 xstar) :=
    (tikhonov_curve_tendsto g hg xstar hxstar Xe hXe).comp hεw
  have φlim : Tendsto φ atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := ‖xstar‖ ^ 2) |>.sub
      (((continuous_norm.tendsto xstar).comp hXlim).pow 2)
    simpa [hφ] using this
  -- integrability
  have aII : ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b →
      IntervalIntegrable (fun s => ε s / s * ‖x s - xstar‖ ^ 2) volume a b :=
    hII (fun s => ε s / s * ‖x s - xstar‖ ^ 2) (wcont.mul ((continuous_norm.comp_continuousOn
      (xcont.sub continuousOn_const)).pow 2))
  have bII : ∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b →
      IntervalIntegrable (fun s => ε s / s * φ s) volume a b := by
    intro a b ha hb
    have : IntervalIntegrable φ volume a b :=
      AntitoneOn.intervalIntegrable (φanti.mono (hsub a b ha hb))
    exact this.continuousOn_mul (wcont.mono (hsub a b ha hb))
  -- abbreviations
  set W : ℝ → ℝ := fun t => ∫ s in t₀..t, ε s / s with hW
  set A : ℝ → ℝ := fun t => ∫ s in t₀..t, ε s / s * ‖x s - xstar‖ ^ 2 with hA
  set B : ℝ → ℝ := fun t => ∫ s in t₀..t, ε s / s * φ s with hB
  -- (46)
  obtain ⟨C, -, hC⟩ := eq_46 g α β t₀ ε ε' u₀ v₀ x xd xdd xstar Xe ht₀ hα hβ hg hε hx hdiv
    hxstar hXe
  have hAB : ∀ t, t₀ ≤ t → A t ≤ 2 * C + B t := by
    intro t ht
    have h := hC t ht
    have heq : (fun s => ε s / s * (hFun x xstar s - 1 / 2 * (‖xstar‖ ^ 2 - ‖Xe (ε s)‖ ^ 2)))
        = fun s => (1/2 : ℝ) * (ε s / s * ‖x s - xstar‖ ^ 2) - (1/2 : ℝ) * (ε s / s * φ s) := by
      funext s; simp only [hFun, hφ]; ring
    rw [heq, intervalIntegral.integral_sub ((aII t₀ t le_rfl ht).const_mul _)
      ((bII t₀ t le_rfl ht).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h
    simp only [hA, hB]
    linarith
  have Ann : ∀ t, t₀ ≤ t → 0 ≤ A t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s hs => mul_nonneg (wnn s hs.1) (sq_nonneg _)
  have Wnn : ∀ t, t₀ ≤ t → 0 ≤ W t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s hs => wnn s hs.1
  have Bnn : ∀ t, t₀ ≤ t → 0 ≤ B t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s hs => mul_nonneg (wnn s hs.1) (φnn s hs.1)
  have hsplit : ∀ (f : ℝ → ℝ), (∀ a b : ℝ, t₀ ≤ a → t₀ ≤ b → IntervalIntegrable f volume a b) →
      ∀ T t, t₀ ≤ T → T ≤ t →
      ∫ s in t₀..t, f s = (∫ s in t₀..T, f s) + ∫ s in T..t, f s := by
    intro f hf T t hT hTt
    rw [intervalIntegral.integral_add_adjacent_intervals (hf t₀ T le_rfl hT)
      (hf T t hT (hT.trans hTt))]
  have hfirst : Tendsto (fun t => (W t)⁻¹ * A t) atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [eventually_ge_atTop t₀] with t ht
      exact lt_of_lt_of_le ha (mul_nonneg (inv_nonneg.2 (Wnn t ht)) (Ann t ht))
    · obtain ⟨T0, hT0⟩ := eventually_atTop.1 (φlim.eventually (gt_mem_nhds (half_pos ha)))
      set T1 := max T0 t₀
      have hT1 : t₀ ≤ T1 := le_max_right _ _
      set K := 2 * C + B T1
      filter_upwards [eventually_ge_atTop T1, hdiv.eventually_ge_atTop (2 * |K| / a + 1)]
        with t ht hWt
      have hWt' : 2 * |K| / a + 1 ≤ W t := hWt
      have h2K : 0 ≤ 2 * |K| / a := div_nonneg (by positivity) ha.le
      have hWpos : 0 < W t := by linarith
      have hBt : B t ≤ B T1 + a / 2 * W t := by
        have e1 := hsplit _ bII T1 t hT1 ht
        have e2 := hsplit _ wII T1 t hT1 ht
        have hmono : ∫ s in T1..t, ε s / s * φ s ≤ ∫ s in T1..t, a / 2 * (ε s / s) := by
          apply intervalIntegral.integral_mono_on ht (bII T1 t hT1 (hT1.trans ht))
            ((wII T1 t hT1 (hT1.trans ht)).const_mul _)
          intro s hs
          have hs0 : t₀ ≤ s := hT1.trans hs.1
          have hφs : φ s < a / 2 := hT0 s ((le_max_left _ _).trans hs.1)
          rw [mul_comm (a / 2)]
          exact mul_le_mul_of_nonneg_left hφs.le (wnn s hs0)
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [hB, hW] at e1 e2 ⊢
        have := Wnn T1 hT1
        simp only [hW] at this
        nlinarith
      have hAt := hAB t (hT1.trans ht)
      have hKlt : K < a / 2 * W t := by
        have h3 : 2 * |K| / a * a = 2 * |K| := div_mul_cancel₀ _ ha.ne'
        have := le_abs_self K
        nlinarith
      rw [inv_mul_lt_iff₀ hWpos]
      nlinarith
  refine ⟨hfirst, ?_⟩
  intro δ hδ
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hcon
  set T2 := max T0 t₀
  have hT2 : t₀ ≤ T2 := le_max_right _ _
  have hlt := hfirst.eventually (gt_mem_nhds (show (0:ℝ) < δ ^ 2 / 2 by positivity))
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((eventually_ge_atTop T2).and
    (hdiv.eventually_gt_atTop (2 * W T2))).and hlt |>.exists
  have hWT2 := Wnn T2 hT2
  have hWt : 0 < W t := by simp only [hW] at hWT2 ⊢; linarith
  have hAt : δ ^ 2 * (W t - W T2) ≤ A t := by
    have e1 := hsplit _ aII T2 t hT2 ht1
    have e2 := hsplit _ wII T2 t hT2 ht1
    have hmono : ∫ s in T2..t, δ ^ 2 * (ε s / s) ≤ ∫ s in T2..t, ε s / s * ‖x s - xstar‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on ht1
        ((wII T2 t hT2 (hT2.trans ht1)).const_mul _) (aII T2 t hT2 (hT2.trans ht1))
      intro s hs
      have hs0 : t₀ ≤ s := hT2.trans hs.1
      have hδs : δ ≤ ‖x s - xstar‖ := not_lt.mp (hT0 s ((le_max_left _ _).trans hs.1))
      rw [mul_comm (δ ^ 2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδs 2) (wnn s hs0)
    rw [intervalIntegral.integral_const_mul] at hmono
    have := Ann T2 hT2
    simp only [hA, hW] at e1 e2 this ⊢
    nlinarith
  have h3 : A t < δ ^ 2 / 2 * W t := by
    have := ht3
    rw [inv_mul_lt_iff₀ hWt] at this
    linarith
  have ht2' : 2 * W T2 < W t := ht2
  nlinarith
