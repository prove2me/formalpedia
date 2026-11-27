-- Prove2me | solution 1 for SinglePointPricing.Det.Supplement.proposition_F_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:22.288799+00:00
-- url     : https://prove2.me/submissions/958a6ec6-7dbd-4698-af10-3fb26061a98f

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_Grid
import Definitions.Def_SinglePointPricing_Det_Supplement_Interval

open SinglePointPricing
open SinglePointPricing.Det
open SinglePointPricing.Det.Supplement

open MeasureTheory

/-- Proposition F-2: one discretized law, independent of nature's value law,
with both error terms and the scale factor `a N / w` in the truncation term. -/
theorem solution (α w ql qh : ℝ)
    (hα : α ∈ Set.Icc 0 1) (hw : 0 < w)
    (hql : ql ∈ Set.Ioo 0 1) (hqh : qh ∈ Set.Ioo 0 1) (hlh : ql ≤ qh)
    (Ψ : Measure ℝ) (hΨ : IsMech Ψ) (N : ℕ) (hN : 1 < N)
    (a : ℕ → ℝ) (ha : IncreasingGrid a (N + 1))
    (ha0 : a 0 = rLow α w ql) (haN : w ≤ a N) :
    ∃ ΨA : Measure ℝ, ΨA ∈ GridClass a (N + 1) ∧
      sInf (ratio Ψ '' FClassI α w ql qh) - gridGap a N / rLow α w ql -
        (if α * GammaAInv α qh * a N < w then 1 else 0) /
          (qh * (1 + (qh⁻¹ - 1) * a N / w)) ≤
        sInf (ratio ΨA '' FClassI α w ql qh) := by
          have Kanti : ∀ s t : ℝ, 0 < s → s ≤ t → GammaAInv α t ≤ GammaAInv α s := by
            intro s t hs hst
            unfold GammaAInv
            split_ifs with h1
            · have := Real.log_le_log hs hst; linarith
            · have hb : 0 < 1 - α := by rcases hα with ⟨_, h⟩; exact sub_pos.mpr (lt_of_le_of_ne h h1)
              have := Real.rpow_le_rpow_of_nonpos hs hst (by linarith : -(1-α) ≤ 0)
              exact div_le_div_of_nonneg_right (by linarith) hb.le
          have Kone : GammaAInv α 1 = 0 := by unfold GammaAInv; split_ifs <;> simp
          have KM : ∀ x y z l : ℝ, 0 < x → 0 < y → 0 < z → 0 ≤ l → l ≤ 1 → x ≤ 1 → y ≤ 1 →
              GammaAInv α z ≤ l * GammaAInv α x + (1 - l) * GammaAInv α y → 1 / z ≤ l / x + (1 - l) / y := by
            intro x y z l hx hy hz hl0 hl1 hx1 hy1 h
            unfold GammaAInv at h
            split_ifs at h with h1
            · have e1 : 1 / z = Real.exp (-Real.log z) := by rw [Real.exp_neg, Real.exp_log hz, one_div]
              have e2 : 1 / x = Real.exp (-Real.log x) := by rw [Real.exp_neg, Real.exp_log hx, one_div]
              have e3 : 1 / y = Real.exp (-Real.log y) := by rw [Real.exp_neg, Real.exp_log hy, one_div]
              rw [e1, div_eq_mul_one_div l, div_eq_mul_one_div (1 - l), e2, e3]
              calc Real.exp (-Real.log z) ≤ Real.exp (l * (-Real.log x) + (1 - l) * (-Real.log y)) :=
                    Real.exp_le_exp.mpr h
                _ ≤ l • Real.exp (-Real.log x) + (1 - l) • Real.exp (-Real.log y) :=
                    convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hl0 (by linarith) (by ring)
                _ = _ := by simp [smul_eq_mul]
            · have hb : 0 < 1 - α := by rcases hα with ⟨_, h⟩; exact sub_pos.mpr (lt_of_le_of_ne h h1)
              set β := 1 - α
              have h' : z ^ (-β) ≤ l * x ^ (-β) + (1 - l) * y ^ (-β) := by
                have := mul_le_mul_of_nonneg_left h hb.le
                have e : ∀ u : ℝ, β * ((u ^ (-β) - 1) / β) = u ^ (-β) - 1 := fun u => by field_simp
                rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm β l, mul_comm β (1 - l), mul_assoc, mul_assoc, e, e, e] at this
                linarith
              have inv : ∀ u : ℝ, 0 < u → (u ^ (-β)) ^ (1 / β) = 1 / u := by
                intro u hu
                rw [← Real.rpow_mul hu.le, show -β * (1 / β) = -1 by field_simp, Real.rpow_neg_one, one_div]
              have hcv := convexOn_rpow (p := 1 / β) (by rw [le_div_iff₀ hb]; linarith [hα.1])
              rw [← inv z hz, div_eq_mul_one_div l, div_eq_mul_one_div (1 - l), ← inv x hx, ← inv y hy]
              calc (z ^ (-β)) ^ (1 / β) ≤ (l * x ^ (-β) + (1 - l) * y ^ (-β)) ^ (1 / β) :=
                    Real.rpow_le_rpow (by positivity) h' (by positivity)
                _ ≤ l • (x ^ (-β)) ^ (1 / β) + (1 - l) • (y ^ (-β)) ^ (1 / β) :=
                    hcv.2 (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity)) hl0 (by linarith) (by ring)
                _ = _ := by simp [smul_eq_mul]
          have K6 : ∀ s t m : ℝ, 0 < t → t ≤ s → s ≤ 1 → 1 ≤ m →
              GammaAInv α t - GammaAInv α s ≤ 1 - 1 / m → s ≤ m * t := by
            intro s t m ht hts hs1 hm h
            have hs : 0 < s := lt_of_lt_of_le ht hts
            have hm0 : 0 < m := by linarith
            have hlog : 1 - 1 / m ≤ Real.log m := by
              have := Real.log_le_sub_one_of_pos (inv_pos.mpr hm0)
              rw [Real.log_inv] at this; rw [one_div]; linarith
            unfold GammaAInv at h
            split_ifs at h with h1
            · have : Real.log s ≤ Real.log (m * t) := by
                rw [Real.log_mul hm0.ne' ht.ne']; linarith
              exact (Real.log_le_log_iff hs (by positivity)).mp this
            · have hb : 0 < 1 - α := by rcases hα with ⟨_, h⟩; exact sub_pos.mpr (lt_of_le_of_ne h h1)
              set β := 1 - α
              have h' : t ^ (-β) - s ^ (-β) ≤ β * Real.log m := by
                have e : (t ^ (-β) - 1) / β - (s ^ (-β) - 1) / β = (t ^ (-β) - s ^ (-β)) / β := by ring
                rw [e, div_le_iff₀ hb] at h; nlinarith
              have hs1' : 1 ≤ s ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by linarith)
              have hmb : β * Real.log m ≤ m ^ β - 1 := by
                have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hm0 β)
                rw [Real.log_rpow hm0] at this; linarith
              have hmb' : 1 ≤ m ^ β := Real.one_le_rpow hm (by linarith)
              have key : (m * t) ^ (-β) ≤ s ^ (-β) := by
                rw [Real.mul_rpow hm0.le ht.le, Real.rpow_neg hm0.le]
                have hmpos : 0 < m ^ β := by positivity
                rw [inv_mul_le_iff₀ hmpos]
                nlinarith
              have := Real.rpow_le_rpow_of_nonpos (by positivity) key (by
                have : 0 < 1 / β := by positivity
                show -(1/β) ≤ 0
                linarith)
              rwa [← Real.rpow_mul hs.le, ← Real.rpow_mul (by positivity),
                show -β * -(1/β) = 1 by field_simp, Real.rpow_one, Real.rpow_one] at this
          have K5 : ∀ s t m : ℝ, 0 < s → 0 < t → t ≤ 1 → 1 ≤ m →
              (m - 1) * (1 + (1 - α) * GammaAInv α t) ≤ GammaAInv α s - GammaAInv α t → m * s ≤ t := by
            intro s t m hs ht ht1 hm h
            have hm0 : 0 < m := by linarith
            unfold GammaAInv at h
            split_ifs at h with h1
            · have hlog : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hm0
              have : Real.log (m * s) ≤ Real.log t := by
                rw [Real.log_mul hm0.ne' hs.ne']; subst h1; simp at h; linarith
              exact (Real.log_le_log_iff (by positivity) ht).mp this
            · have hb : 0 < 1 - α := by rcases hα with ⟨_, h⟩; exact sub_pos.mpr (lt_of_le_of_ne h h1)
              set β := 1 - α
              have h' : β * (m - 1) * t ^ (-β) ≤ s ^ (-β) - t ^ (-β) := by
                have e : (m - 1) * (1 + β * ((t ^ (-β) - 1) / β)) = (m - 1) * t ^ (-β) := by field_simp; ring
                have e2 : (s ^ (-β) - 1) / β - (t ^ (-β) - 1) / β = (s ^ (-β) - t ^ (-β)) / β := by ring
                rw [e, e2, le_div_iff₀ hb] at h; nlinarith
              have hbern : m ^ β ≤ 1 + β * (m - 1) := by
                have := rpow_one_add_le_one_add_mul_self (s := m - 1) (by linarith) hb.le (by linarith [hα.1])
                simpa using this
              have htpos : 0 < t ^ (-β) := by positivity
              have key : (t / m) ^ (-β) ≤ s ^ (-β) := by
                rw [Real.div_rpow ht.le hm0.le, Real.rpow_neg hm0.le, div_inv_eq_mul]
                nlinarith
              have := Real.rpow_le_rpow_of_nonpos (by positivity) key (by
                have : 0 < 1 / β := by positivity
                show -(1/β) ≤ 0
                linarith)
              rw [← Real.rpow_mul hs.le, ← Real.rpow_mul (by positivity),
                show -β * -(1/β) = 1 by field_simp, Real.rpow_one, Real.rpow_one] at this
              rwa [le_div_iff₀ hm0, mul_comm] at this
          have ALG1 : ∀ A s x a : ℝ, 0 < A → 0 < s → 0 < x →
              1 / A ≤ (a / x) / s + (1 - a / x) / 1 → x * s ≤ A * (a + (x - a) * s) := by
            intro A s x a hA hs hx h
            have e : A * x * s * ((a / x) / s + (1 - a / x) / 1) = A * (a + (x - a) * s) := by
              field_simp
            have e2 : A * x * s * (1 / A) = x * s := by field_simp
            calc x * s = A * x * s * (1 / A) := e2.symm
              _ ≤ A * x * s * ((a / x) / s + (1 - a / x) / 1) :=
                  mul_le_mul_of_nonneg_left h (by positivity)
              _ = _ := e
          have ALG2 : ∀ x s a A w q : ℝ, 0 < w → w ≤ a → a ≤ x → 0 < q → q < 1 → 0 ≤ s → 0 < A →
              x * s ≤ A * (a + (x - a) * s) → x * s * (1 - q) ≤ q * w →
              x * s - a * A ≤ x * s / (q * (1 + (q⁻¹ - 1) * a / w)) := by
            intro x s a A w q hw hwa hax hq0 hq1 hs hA h1 h2
            have hD : q * (1 + (q⁻¹ - 1) * a / w) = (q * w + (1 - q) * a) / w := by
              field_simp
            have hDpos : 0 < q * w + (1 - q) * a := by
              have : 0 ≤ (1 - q) * a := mul_nonneg (by linarith only [hq1]) (by linarith only [hw, hwa])
              have : 0 < q * w := mul_pos hq0 hw
              linarith only [this, ‹0 ≤ (1 - q) * a›]
            rw [hD, div_div_eq_mul_div, le_div_iff₀ hDpos]
            have hDw : 0 ≤ (1 - q) * (a - w) := mul_nonneg (by linarith only [hq1]) (by linarith only [hwa])
            have hr : x * s - a * A ≤ A * ((x - a) * s) := by linarith only [h1]
            have p1 := mul_le_mul_of_nonneg_right hr hDw
            have p2 : 0 ≤ a * s * A * ((1 - q) * (a - w)) :=
              mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hw, hwa]) hs) hA.le) hDw
            have p3 : A * (x * s * (1 - q)) * (a - w) ≤ A * (q * w) * (a - w) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hA.le) (by linarith only [hwa])
            have p4 : A * w * (q * (a - w)) ≤ A * w * a :=
              mul_le_mul_of_nonneg_left (by linarith only [hDw, hw, hwa]) (mul_nonneg hA.le hw.le)
            linarith only [p1, p2, p3, p4]
          have ALG3 : ∀ (x a w c Ha Hx Hw : ℝ), 0 < w → 0 < a → a ≤ x → w ≤ α * c * a → c ≤ Hw →
              Hw ≤ w / a * Ha → Ha ≤ a / x * Hx → (x / a - 1) * (1 + (1 - α) * Ha) ≤ Hx - Ha := by
            intro x a w c Ha Hx Hw hw ha hax hwc hcH hHw hHa
            have hx : 0 < x := lt_of_lt_of_le ha hax
            have h1 : a * Hw ≤ w * Ha := by
              have := mul_le_mul_of_nonneg_left hHw ha.le
              rwa [← mul_assoc, mul_div_cancel₀ w ha.ne'] at this
            have h2 : x * Ha ≤ a * Hx := by
              have := mul_le_mul_of_nonneg_left hHa hx.le
              rwa [← mul_assoc, mul_div_cancel₀ a hx.ne'] at this
            have h3 : 1 ≤ α * Ha := by
              have q1 := mul_le_mul_of_nonneg_left hcH (mul_nonneg hα.1 ha.le)
              have q2 := mul_le_mul_of_nonneg_left h1 hα.1
              have : w * 1 ≤ w * (α * Ha) := by linarith only [hwc, q1, q2]
              exact le_of_mul_le_mul_left this hw
            have hm : 0 ≤ x / a - 1 := by rw [sub_nonneg, le_div_iff₀ ha]; linarith only [hax]
            have h4 : x * Ha / a ≤ Hx := by rw [div_le_iff₀ ha]; linarith only [h2]
            have e : (x / a - 1) * Ha = x * Ha / a - Ha := by ring
            have h5 : (x / a - 1) * (1 + (1 - α) * Ha) ≤ (x / a - 1) * (α * Ha + (1 - α) * Ha) :=
              mul_le_mul_of_nonneg_left (by linarith only [h3]) hm
            have e2 : (x / a - 1) * (α * Ha + (1 - α) * Ha) = (x / a - 1) * Ha := by ring
            linarith only [h5, e, e2, h4]
          have hα0 : 0 ≤ α := hα.1
          have hα1 : α ≤ 1 := hα.2
          have hc0 : 0 ≤ GammaAInv α ql := by
            have := Kanti ql 1 hql.1 hql.2.le; rw [Kone] at this; exact this
          have ha0pos : 0 < rLow α w ql := by unfold rLow; positivity
          have ha0w : rLow α w ql * (GammaAInv α ql + 1) = w := by
            unfold rLow; field_simp
          have hmono : ∀ i j, i ≤ j → j ≤ N → a i ≤ a j := by
            intro i j hij hj
            rcases eq_or_lt_of_le hij with h | h
            · rw [h]
            · exact (ha i j h (by omega)).le
          have hapos : ∀ i, i ≤ N → 0 < a i := by
            intro i hi
            have := hmono 0 i (Nat.zero_le _) hi
            rw [ha0] at this; linarith
          have hgap : ∀ i, i < N → a (i + 1) - a i ≤ gridGap a N := by
            intro i hi
            unfold gridGap
            apply le_csSup (Set.toFinite _).bddAbove
            exact ⟨⟨i, hi⟩, Set.mem_univ _, rfl⟩
          have hgap0 : 0 ≤ gridGap a N := by
            have := hgap 0 (by omega)
            have := hmono 0 1 (by omega) (by omega)
            linarith
          have hden : 0 < qh * (1 + (qh⁻¹ - 1) * a N / w) := by
            have : 0 ≤ qh⁻¹ - 1 := by
              rw [sub_nonneg]; exact one_le_inv_iff₀.mpr ⟨hqh.1, hqh.2.le⟩
            have := hapos N le_rfl
            have : 0 ≤ (qh⁻¹ - 1) * a N / w := by positivity
            have := hqh.1
            positivity
          set T := (if α * GammaAInv α qh * a N < w then (1:ℝ) else 0) /
                  (qh * (1 + (qh⁻¹ - 1) * a N / w)) with hT
          have hT0 : 0 ≤ T := by
            apply div_nonneg _ hden.le; split_ifs <;> norm_num
          set E := gridGap a N / rLow α w ql + T with hE
          have hE0 : 0 ≤ E := by have := div_nonneg hgap0 ha0pos.le; linarith
          -- the rounding index
          let J : ℝ → ℕ := fun x => Nat.findGreatest (fun j => a j ≤ x) N
          have hJmono : Monotone J := fun x y hxy =>
            Nat.findGreatest_mono_left (fun j h => le_trans h hxy) N
          have hJmeas : Measurable J := hJmono.measurable
          have hJle : ∀ x, J x ≤ N := fun x => Nat.findGreatest_le N
          have hJspec : ∀ x, J x ≠ 0 → a (J x) ≤ x := fun x h =>
            Nat.findGreatest_spec (P := fun j => a j ≤ x) (m := J x) (hJle x) (Nat.findGreatest_eq_iff.mp rfl |>.2.1 h)
          have hJgreat : ∀ x, J x < N → x < a (J x + 1) := fun x h =>
            lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun j => a j ≤ x) (Nat.lt_succ_self _) (by omega))
          let pw : ℕ → ℝ := fun j => Ψ.real (J ⁻¹' {j})
          have hΨp := hΨ.1
          have hpre : ∀ j, MeasurableSet (J ⁻¹' {j}) := fun j => hJmeas (measurableSet_singleton j)
          have hsum : ∑ j ∈ Finset.range (N + 1), pw j = 1 := by
            have h1 : ∑ j ∈ Finset.range (N + 1), Ψ (J ⁻¹' {j}) = 1 := by
              rw [sum_measure_preimage_singleton _ (fun j _ => hpre j)]
              have : J ⁻¹' ↑(Finset.range (N + 1)) = Set.univ := by
                ext x; simp [Finset.mem_range, Nat.lt_succ_iff, hJle x]
              rw [this, measure_univ]
            have := congrArg ENNReal.toReal h1
            rw [ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at this
            simpa [pw, measureReal_def] using this
          refine ⟨gridMech a pw (N + 1), ⟨⟨?_, ?_⟩, pw, ⟨fun j _ => measureReal_nonneg, hsum⟩, rfl⟩, ?_⟩
          · constructor
            simp only [gridMech, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
              measure_univ, smul_eq_mul, mul_one]
            rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => measureReal_nonneg), hsum, ENNReal.ofReal_one]
          · simp only [gridMech, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
            apply Finset.sum_eq_zero
            intro j hj
            have : 0 < a j := hapos j (by simp at hj; omega)
            rw [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator_of_notMem (by simp; linarith)]
            simp
          -- main per-μ estimate
          have key : ∀ μ ∈ FClassI α w ql qh, 0 ≤ ratio Ψ μ ∧
              ratio Ψ μ - E ≤ ratio (gridMech a pw (N + 1)) μ := by
            rintro μ ⟨⟨hprob, hneg, hint, hmean⟩, hSR, hsw⟩
            have sf_anti : ∀ x y, x ≤ y → sf μ y ≤ sf μ x := fun x y h =>
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ici_subset_Ici.2 h))
            have sf_nn : ∀ x, 0 ≤ sf μ x := fun x => ENNReal.toReal_nonneg
            have sf_le1 : ∀ x, sf μ x ≤ 1 := fun x => by
              unfold sf; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
            have sf0 : sf μ 0 = 1 := by
              unfold sf
              have : μ (Set.Ici 0) = 1 := by
                rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, hneg, tsub_zero]
              simp [this]
            have hmeas_sf : Measurable (sf μ) := (Antitone.measurable (fun x y h => sf_anti x y h))
            have markov : ∀ x, 0 ≤ x → x * sf μ x ≤ ∫ v, v ∂μ := by
              intro x hx
              have hnn : 0 ≤ᵐ[μ] (fun v : ℝ => v) := by
                rw [Filter.EventuallyLE, ae_iff]
                refine le_antisymm (le_trans (measure_mono ?_) hneg.le) bot_le
                intro v hv; simp at hv; exact hv
              have := mul_meas_ge_le_integral_of_nonneg hnn hint x
              simpa [sf, measureReal_def, Set.Ici] using this
            have hO : ∀ x, 0 ≤ x → x * sf μ x ≤ opt μ := fun x hx =>
              le_csSup ⟨∫ v, v ∂μ, by rintro _ ⟨y, hy, rfl⟩; exact markov y hy⟩ ⟨x, hx, rfl⟩
            have hOpos : 0 < opt μ := by
              have := hO w hw.le
              have : 0 < w * sf μ w := mul_pos hw (lt_of_lt_of_le hql.1 hsw.1)
              linarith
            set O := opt μ
            -- regularity
            let H : ℝ → ℝ := fun v => GammaAInv α (sf μ v)
            have hcv : ∀ x y θ : ℝ, 0 ≤ x → 0 < sf μ x → 0 ≤ y → 0 < sf μ y → 0 ≤ θ → θ ≤ 1 →
                H (θ * x + (1 - θ) * y) ≤ θ * H x + (1 - θ) * H y := by
              intro x y θ hx hsx hy hsy h0 h1
              have := hSR.2 ⟨hx, hsx⟩ ⟨hy, hsy⟩ h0 (show (0:ℝ) ≤ 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
              simpa [smul_eq_mul] using this
            have H0 : H 0 = 0 := by simp [H, sf0, Kone]
            have pt : ∀ x, 0 ≤ x → x * sf μ x - E * O ≤ a (J x) * sf μ (a (J x)) := by
              intro x hx
              have hO' := hO x hx
              have hTO : 0 ≤ T * O := mul_nonneg hT0 hOpos.le
              have hgO : 0 ≤ gridGap a N / rLow α w ql * O :=
                mul_nonneg (div_nonneg hgap0 ha0pos.le) hOpos.le
              have hEsplit : E * O = gridGap a N / rLow α w ql * O + T * O := by rw [hE]; ring
              have hjN : J x ≤ N := hJle x
              have hajpos : 0 < a (J x) := hapos (J x) hjN
              have hsw0 : 0 < sf μ w := lt_of_lt_of_le hql.1 hsw.1
              by_cases hlow : x < a 0
              · have hj0 : J x = 0 := by
                  by_contra h
                  have h1 := hJspec x h
                  have h2 := hmono 0 (J x) (Nat.zero_le _) hjN
                  linarith only [h1, h2, hlow]
                rw [hj0]
                suffices x * sf μ x ≤ a 0 * sf μ (a 0) by linarith only [this, hgO, hTO, hEsplit]
                have hA0 : 0 < a 0 := hapos 0 (Nat.zero_le _)
                rcases eq_or_lt_of_le hx with hx0 | hxpos
                · rw [← hx0, zero_mul]; exact mul_nonneg hA0.le (sf_nn _)
                rcases eq_or_lt_of_le (sf_nn x) with hs0 | hspos
                · rw [← hs0, mul_zero]; exact mul_nonneg hA0.le (sf_nn _)
                have hAw : a 0 ≤ w := by
                  have := mul_nonneg ha0pos.le hc0
                  rw [ha0]; linarith only [this, ha0w]
                have hsA : 0 < sf μ (a 0) := lt_of_lt_of_le hsw0 (sf_anti _ _ hAw)
                have hwx : 0 < w - x := by linarith only [hlow, hAw]
                have hθ0 : 0 ≤ (w - a 0) / (w - x) := div_nonneg (by linarith only [hAw]) hwx.le
                have hθ1 : (w - a 0) / (w - x) ≤ 1 := by rw [div_le_one hwx]; linarith only [hlow]
                have hθm : (w - a 0) / (w - x) * (w - x) = w - a 0 := div_mul_cancel₀ _ hwx.ne'
                have hpt : (w - a 0) / (w - x) * x + (1 - (w - a 0) / (w - x)) * w = a 0 := by
                  linear_combination -hθm
                have hc := hcv x w ((w - a 0) / (w - x)) hx hspos hw.le hsw0 hθ0 hθ1
                rw [hpt] at hc
                have hHw : H w ≤ GammaAInv α ql := Kanti ql (sf μ w) hql.1 hsw.1
                have hHx : 0 ≤ H x := by
                  have := Kanti (sf μ x) 1 hspos (sf_le1 x); rw [Kone] at this; exact this
                have h1θ : 1 - (w - a 0) / (w - x) = (a 0 - x) / (w - x) := by
                  rw [eq_div_iff hwx.ne']; linear_combination -hθm
                have hAc : a 0 * GammaAInv α ql = w - a 0 := by rw [ha0]; linarith only [ha0w]
                have hd : H (a 0) - H x ≤ 1 - 1 / (a 0 / x) := by
                  have hθ1' : 0 ≤ 1 - (w - a 0) / (w - x) := by linarith only [hθ1]
                  have q1 := mul_le_mul_of_nonneg_left hHw hθ1'
                  have q2 := mul_nonneg hθ1' hHx
                  have e1 : H (a 0) - H x ≤ (1 - (w - a 0) / (w - x)) * GammaAInv α ql := by
                    linarith only [hc, q1, q2]
                  rw [h1θ] at e1
                  have e3 : 1 - 1 / (a 0 / x) = (a 0 - x) / a 0 := by
                    rw [one_div_div, sub_div, div_self hA0.ne']
                  have e2 : (a 0 - x) / (w - x) * GammaAInv α ql ≤ (a 0 - x) / a 0 := by
                    rw [div_mul_eq_mul_div, div_le_div_iff₀ hwx hA0]
                    have h4 : a 0 * GammaAInv α ql ≤ w - x := by linarith only [hAc, hlow]
                    have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ a 0 - x by linarith only [hlow])
                    linarith only [h5]
                  linarith only [e1, e2, e3]
                have := K6 (sf μ x) (sf μ (a 0)) (a 0 / x) hsA (sf_anti _ _ hlow.le) (sf_le1 x)
                  (by rw [le_div_iff₀ hxpos]; linarith only [hlow]) hd
                calc x * sf μ x ≤ x * (a 0 / x * sf μ (a 0)) := mul_le_mul_of_nonneg_left this hx
                  _ = a 0 * sf μ (a 0) := by
                    rw [← mul_assoc, mul_div_cancel₀ (a 0) hxpos.ne']
              · push_neg at hlow
                have hajx : a (J x) ≤ x := by
                  by_cases h : J x = 0
                  · rw [h]; exact hlow
                  · exact hJspec x h
                by_cases hjlt : J x < N
                · have hxlt := hJgreat x hjlt
                  have hg := hgap (J x) hjlt
                  have h1 : a (J x) * sf μ x ≤ a (J x) * sf μ (a (J x)) :=
                    mul_le_mul_of_nonneg_left (sf_anti _ _ hajx) hajpos.le
                  have h2 : (x - a (J x)) * sf μ x ≤ gridGap a N * sf μ x :=
                    mul_le_mul_of_nonneg_right (by linarith only [hxlt, hg]) (sf_nn x)
                  have h3 : gridGap a N * sf μ x ≤ gridGap a N / rLow α w ql * O := by
                    rw [div_mul_eq_mul_div, le_div_iff₀ ha0pos]
                    have : rLow α w ql * sf μ x ≤ O :=
                      le_trans (mul_le_mul_of_nonneg_right (by rw [← ha0]; exact hlow) (sf_nn x)) hO'
                    have := mul_le_mul_of_nonneg_left this hgap0
                    linarith only [this]
                  linarith only [h1, h2, h3, hEsplit, hTO]
                · have hjN' : J x = N := by omega
                  rw [hjN'] at hajx ⊢
                  suffices x * sf μ x - a N * sf μ (a N) ≤ T * O by linarith only [this, hEsplit, hgO]
                  have haNpos : 0 < a N := hapos N le_rfl
                  have hxpos : 0 < x := lt_of_lt_of_le haNpos hajx
                  rcases eq_or_lt_of_le (sf_nn x) with hs0 | hspos
                  · rw [← hs0, mul_zero]
                    linarith only [mul_nonneg haNpos.le (sf_nn (a N)), hTO]
                  have hApos : 0 < sf μ (a N) := lt_of_lt_of_le hspos (sf_anti _ _ hajx)
                  have hone : (0:ℝ) < sf μ 0 := by rw [sf0]; exact one_pos
                  have cvx : ∀ z y, 0 < z → 0 < sf μ z → 0 ≤ y → y ≤ z → H y ≤ y / z * H z := by
                    intro z y hz hsz hy hyz
                    have h := hcv z 0 (y / z) hz.le hsz le_rfl hone (div_nonneg hy hz.le)
                      (by rw [div_le_one hz]; exact hyz)
                    simp only [H0, mul_zero, add_zero] at h
                    rwa [div_mul_cancel₀ y hz.ne'] at h
                  have hwx : w ≤ x := le_trans haN hajx
                  have hHa := cvx x (a N) hxpos hspos haNpos.le hajx
                  have hHw := cvx x w hxpos hspos hw.le hwx
                  have G1 : 1 / sf μ (a N) ≤ (a N / x) / sf μ x + (1 - a N / x) / 1 := by
                    apply KM (sf μ x) 1 (sf μ (a N)) (a N / x) hspos one_pos hApos
                      (div_nonneg haNpos.le hxpos.le) (by rw [div_le_one hxpos]; exact hajx) (sf_le1 x) le_rfl
                    rw [Kone, mul_zero, add_zero]; exact hHa
                  have G2 : 1 / sf μ w ≤ (w / x) / sf μ x + (1 - w / x) / 1 := by
                    apply KM (sf μ x) 1 (sf μ w) (w / x) hspos one_pos hsw0
                      (div_nonneg hw.le hxpos.le) (by rw [div_le_one hxpos]; exact hwx) (sf_le1 x) le_rfl
                    rw [Kone, mul_zero, add_zero]; exact hHw
                  have A1 := ALG1 _ _ _ _ hApos hspos hxpos G1
                  have A2 := ALG1 _ _ _ _ hsw0 hspos hxpos G2
                  have hfac : 0 ≤ w + (x - w) * sf μ x :=
                    add_nonneg hw.le (mul_nonneg (by linarith only [hwx]) hspos.le)
                  have q1 := mul_le_mul_of_nonneg_right hsw.2 hfac
                  have q2 : 0 ≤ qh * w * sf μ x := mul_nonneg (mul_nonneg hqh.1.le hw.le) hspos.le
                  have B2 : x * sf μ x * (1 - qh) ≤ qh * w := by linarith only [A2, q1, q2]
                  by_cases hind : α * GammaAInv α qh * a N < w
                  · have hTe : T * (x * sf μ x) = x * sf μ x / (qh * (1 + (qh⁻¹ - 1) * a N / w)) := by
                      rw [hT, if_pos hind, one_div_mul_eq_div]
                    have := ALG2 x (sf μ x) (a N) (sf μ (a N)) w qh hw haN hajx hqh.1 hqh.2 hspos.le hApos A1 B2
                    have := mul_le_mul_of_nonneg_left hO' hT0
                    linarith only [this, ‹x * sf μ x - a N * sf μ (a N) ≤ _›, hTe]
                  · push_neg at hind
                    have hT00 : T = 0 := by rw [hT, if_neg (not_lt.mpr hind), zero_div]
                    rw [hT00, zero_mul]
                    have hcw : GammaAInv α qh ≤ H w := Kanti (sf μ w) qh hsw0 hsw.2
                    have hHwa := cvx (a N) w haNpos hApos hw.le haN
                    have h3 := ALG3 x (a N) w (GammaAInv α qh) (H (a N)) (H x) (H w) hw haNpos hajx
                      (by linarith only [hind]) hcw hHwa hHa
                    have hm1 : 1 ≤ x / a N := by rw [le_div_iff₀ haNpos]; linarith only [hajx]
                    have hK := K5 (sf μ x) (sf μ (a N)) (x / a N) hspos hApos (sf_le1 _) hm1 h3
                    have e : a N * (x / a N * sf μ x) = x * sf μ x := by
                      rw [← mul_assoc, mul_div_cancel₀ x haNpos.ne']
                    have := mul_le_mul_of_nonneg_left hK haNpos.le
                    linarith only [this, e]
            -- integrals
            have hf_int : Integrable (fun x => x * sf μ x) Ψ := by
              refine Integrable.of_bound (C := O) ((measurable_id.mul hmeas_sf).aestronglyMeasurable) ?_
              have : ∀ᵐ x ∂Ψ, 0 ≤ x := by
                rw [ae_iff]; refine le_antisymm (le_trans (measure_mono ?_) hΨ.2.le) bot_le
                intro v hv; simp at hv; exact hv
              filter_upwards [this] with x hx
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (sf_nn x))]
              exact hO x hx
            have hA : ∫ x, x * sf μ x ∂(gridMech a pw (N + 1)) =
                ∑ j ∈ Finset.range (N + 1), pw j * (a j * sf μ (a j)) := by
              unfold gridMech
              rw [integral_finset_sum_measure]
              · apply Finset.sum_congr rfl; intro j _
                rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal measureReal_nonneg, smul_eq_mul]
              · intro j _
                exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
            have hG : ∫ x, a (J x) * sf μ (a (J x)) ∂Ψ =
                ∑ j ∈ Finset.range (N + 1), pw j * (a j * sf μ (a j)) := by
              have e : (fun x => a (J x) * sf μ (a (J x))) = fun x => ∑ j ∈ Finset.range (N + 1),
                  (J ⁻¹' {j}).indicator (fun _ => a j * sf μ (a j)) x := by
                funext x
                rw [Finset.sum_eq_single (J x)]
                · simp
                · intro b _ hb; simp [Set.indicator, Ne.symm hb]
                · intro h; simp [Finset.mem_range] at h; have := hJle x; omega
              rw [e, integral_finset_sum]
              · apply Finset.sum_congr rfl; intro j _
                rw [integral_indicator_const _ (hpre j), smul_eq_mul]
              · intro j _
                exact (integrable_const _).indicator (hpre j)
            have hGint : Integrable (fun x => a (J x) * sf μ (a (J x))) Ψ := by
              have hm : Measurable (fun x => a (J x)) := (measurable_from_nat (f := a)).comp hJmeas
              refine Integrable.of_bound (C := O) ((hm.mul (hmeas_sf.comp hm)).aestronglyMeasurable) ?_
              filter_upwards with x
              have := hapos (J x) (hJle x)
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg this.le (sf_nn _))]
              exact hO _ this.le
            have hle : ∫ x, x * sf μ x ∂Ψ - E * O ≤ ∫ x, a (J x) * sf μ (a (J x)) ∂Ψ := by
              have h2 : ∫ x, (x * sf μ x - E * O) ∂Ψ ≤ ∫ x, a (J x) * sf μ (a (J x)) ∂Ψ := by
                apply integral_mono_ae (hf_int.sub (integrable_const _)) hGint
                have : ∀ᵐ x ∂Ψ, 0 ≤ x := by
                  rw [ae_iff]; refine le_antisymm (le_trans (measure_mono ?_) hΨ.2.le) bot_le
                  intro v hv; simp at hv; exact hv
                filter_upwards [this] with x hx
                exact pt x hx
              rw [integral_sub hf_int (integrable_const _)] at h2
              simpa using h2
            refine ⟨?_, ?_⟩
            · unfold ratio
              apply div_nonneg _ hOpos.le
              apply integral_nonneg_of_ae
              have : ∀ᵐ x ∂Ψ, 0 ≤ x := by
                rw [ae_iff]; refine le_antisymm (le_trans (measure_mono ?_) hΨ.2.le) bot_le
                intro v hv; simp at hv; exact hv
              filter_upwards [this] with x hx
              exact mul_nonneg hx (sf_nn x)
            · unfold ratio
              rw [hA, ← hG]
              rw [sub_le_iff_le_add, div_add' _ _ _ hOpos.ne', div_le_div_iff_of_pos_right hOpos]
              linarith
          by_cases hF : (FClassI α w ql qh).Nonempty
          · apply le_csInf (hF.image _)
            rintro _ ⟨μ, hμ, rfl⟩
            have h1 := key μ hμ
            have h2 : sInf (ratio Ψ '' FClassI α w ql qh) ≤ ratio Ψ μ := by
              refine csInf_le ⟨0, ?_⟩ ⟨μ, hμ, rfl⟩
              rintro _ ⟨ν, hν, rfl⟩
              exact (key ν hν).1
            have : sInf (ratio Ψ '' FClassI α w ql qh) - gridGap a N / rLow α w ql - T =
              sInf (ratio Ψ '' FClassI α w ql qh) - E := by rw [hE]; ring
            rw [this]; linarith [h1.2]
          · rw [Set.not_nonempty_iff_eq_empty] at hF
            rw [hF, Set.image_empty, Set.image_empty, Real.sInf_empty]
            have := div_nonneg hgap0 ha0pos.le
            linarith
