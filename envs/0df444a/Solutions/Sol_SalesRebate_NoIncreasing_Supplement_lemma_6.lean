-- Prove2me | solution 1 for SalesRebate.NoIncreasing.Supplement.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:34.410491+00:00
-- url     : https://prove2.me/submissions/91ef7337-583d-4848-8372-d34c6f0cef7b

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

open SalesRebate
open SalesRebate.NoIncreasing
open SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hsq : a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2) :
    stdNormalCDF a / stdNormalPDF a * (stdNormalCDF d / stdNormalPDF d) ≤
      stdNormalCDF b / stdNormalPDF b * (stdNormalCDF c / stdNormalPDF c) := by
        obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, E = fun z => Real.exp (-z ^ 2 / 2) := ⟨_, rfl⟩
        obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun x => ∫ z in Set.Iic x, E z := ⟨_, rfl⟩
        have hEint : Integrable E := by
          have := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)
          refine this.congr (Filter.Eventually.of_forall fun z => ?_)
          simp only [hE]; ring_nf
        have hEcont : Continuous E := by rw [hE]; fun_prop
        have hEpos : ∀ z, 0 < E z := fun z => by rw [hE]; exact Real.exp_pos _
        have hGeq : ∀ x, G x = G 0 + ∫ z in (0:ℝ)..x, E z := by
          intro x
          have := intervalIntegral.integral_Iic_sub_Iic (f := E) (μ := volume) (a := 0) (b := x)
            hEint.integrableOn hEint.integrableOn
          simp only [hG]; linarith
        have hGderiv : ∀ x, HasDerivAt G (E x) x := by
          intro x
          have h1 := (hEcont.integral_hasStrictDerivAt 0 x).hasDerivAt
          have : G = fun u => G 0 + ∫ z in (0:ℝ)..u, E z := funext hGeq
          rw [this]
          exact h1.const_add _
        have hGpos : ∀ x, 0 < G x := by
          intro x
          simp only [hG]
          rw [integral_pos_iff_support_of_nonneg (fun z => (hEpos z).le) hEint.integrableOn]
          have hsupp : Function.support E = Set.univ := by
            ext z; simp [(hEpos z).ne']
          rw [hsupp, Measure.restrict_apply_univ, Real.volume_Iic]
          simp
        have hGmono : Monotone G :=
          monotone_of_deriv_nonneg (fun x => (hGderiv x).differentiableAt)
            (fun x => by rw [(hGderiv x).deriv]; exact (hEpos x).le)
        have hGcont : Continuous G := continuous_iff_continuousAt.2 fun x => (hGderiv x).continuousAt
        -- reduction
        have hC : 0 < 1 / Real.sqrt (2 * Real.pi) := by positivity
        have hratio : ∀ x, stdNormalCDF x / stdNormalPDF x = G x / E x := by
          intro x
          simp only [stdNormalCDF, stdNormalPDF, hG, hE]
          rw [mul_div_mul_left _ _ hC.ne']
        rw [hratio, hratio, hratio, hratio]
        have hEprod : E a * E d = E b * E c := by
          simp only [hE]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          linarith
        have hkey : G a * G d ≤ G b * G c := by
          obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, k = fun t => Real.log (G (Real.sqrt t)) := ⟨_, rfl⟩
          have hkder : ∀ t, 0 < t →
              HasDerivAt k (E (Real.sqrt t) * (1 / (2 * Real.sqrt t)) / G (Real.sqrt t)) t := by
            intro t ht
            have h1 := (hGderiv (Real.sqrt t)).comp t (Real.hasDerivAt_sqrt ht.ne')
            have h2 := h1.log (hGpos _).ne'
            rw [hk]
            exact h2
          have hconc : ConcaveOn ℝ (Set.Ici (0:ℝ)) k := by
            apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
            · rw [hk]
              exact (Continuous.log (hGcont.comp Real.continuous_sqrt)
                (fun t => (hGpos _).ne')).continuousOn
            · rw [interior_Ici]
              intro t ht
              exact (hkder t ht).differentiableAt.differentiableWithinAt
            · rw [interior_Ici]
              intro s hs t ht hst
              simp only [Set.mem_Ioi] at hs ht
              rw [(hkder s hs).deriv, (hkder t ht).deriv]
              have hx : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
              have hxy : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
              set x := Real.sqrt s
              set y := Real.sqrt t
              have hEy : E y ≤ E x := by
                simp only [hE]
                apply Real.exp_le_exp.2
                nlinarith
              rw [mul_one_div, mul_one_div, div_div, div_div]
              apply div_le_div₀ (hEpos x).le hEy (by have := hGpos x; positivity)
              have := hGmono hxy
              have := hGpos x
              nlinarith
          have hb : 0 ≤ b := ha.trans hab
          have hc : 0 ≤ c := hb.trans hbc
          have hd : 0 ≤ d := hc.trans hcd
          have hs_u : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
          have hu_v : b ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hb hbc 2
          have hv_t : c ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hc hcd 2
          have hkx : ∀ x, 0 ≤ x → k (x ^ 2) = Real.log (G x) := by
            intro x hx
            rw [hk]
            simp only
            rw [Real.sqrt_sq hx]
          have hlog : Real.log (G a) + Real.log (G d) ≤ Real.log (G b) + Real.log (G c) := by
            rcases eq_or_lt_of_le (hs_u.trans (hu_v.trans hv_t)) with heq | hlt
            · have had : a = d := by nlinarith
              have h1 : a = b := le_antisymm hab (by rw [had]; exact hbc.trans hcd)
              have h2 : b = c := le_antisymm hbc (by rw [← h1, had]; exact hcd)
              rw [← h1, ← h2] at *
              rw [← had]
            · set s := a ^ 2
              set t := d ^ 2
              set u := b ^ 2
              set v := c ^ 2
              have hts : 0 < t - s := by linarith
              set α := (t - u) / (t - s) with hα
              set β := (u - s) / (t - s) with hβ
              have hα0 : 0 ≤ α := div_nonneg (by linarith) hts.le
              have hβ0 : 0 ≤ β := div_nonneg (by linarith) hts.le
              have hαβ : α + β = 1 := by
                rw [hα, hβ, ← add_div]; field_simp; ring
              have hs0 : s ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by positivity)
              have ht0 : t ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by positivity)
              have e1 : α • s + β • t = u := by
                simp only [smul_eq_mul]; rw [hα, hβ]; field_simp; ring
              have e2 : β • s + α • t = v := by
                rw [show v = s + t - u by linarith]; simp only [smul_eq_mul]; rw [hα, hβ]; field_simp; ring
              have h1 := hconc.2 hs0 ht0 hα0 hβ0 hαβ
              have h2 := hconc.2 hs0 ht0 hβ0 hα0 (by linarith)
              rw [e1] at h1
              rw [e2] at h2
              simp only [smul_eq_mul] at h1 h2
              have hks := hkx a ha
              have hkt := hkx d hd
              have hku := hkx b hb
              have hkv := hkx c hc
              have : (α + β) * (k s + k t) ≤ k u + k v := by nlinarith
              rw [hαβ, one_mul] at this
              linarith
          rw [← Real.log_mul (hGpos a).ne' (hGpos d).ne', ← Real.log_mul (hGpos b).ne' (hGpos c).ne'] at hlog
          exact (Real.log_le_log_iff (mul_pos (hGpos a) (hGpos d)) (mul_pos (hGpos b) (hGpos c))).1 hlog
        rw [div_mul_div_comm, div_mul_div_comm, hEprod]
        exact div_le_div_of_nonneg_right hkey (mul_pos (hEpos b) (hEpos c)).le
