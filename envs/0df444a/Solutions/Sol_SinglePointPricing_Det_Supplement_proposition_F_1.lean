-- Prove2me | solution 1 for SinglePointPricing.Det.Supplement.proposition_F_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:58.371074+00:00
-- url     : https://prove2.me/submissions/d259beb9-d774-49d2-8e00-5534d79c5869

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_IntervalFamily

open SinglePointPricing
open SinglePointPricing.Det
open SinglePointPricing.Det.Supplement

open MeasureTheory

/-- Proposition F-1, including the singleton-information case and arbitrary
(possibly empty) subclasses of pricing mechanisms. -/
theorem solution (α w ql qh : ℝ)
    (hα : α ∈ Set.Icc 0 1) (hw : 0 < w)
    (hql : ql ∈ Set.Ioo 0 1) (hqh : qh ∈ Set.Ioo 0 1) (hlh : ql ≤ qh)
    (P' : Set (Measure ℝ)) (hP : P' ⊆ {Ψ | IsMech Ψ}) :
    maximin P' (FClassI α w ql qh) = maximin P' (SFamilyI α w ql qh) := by
      obtain ⟨hα0, hα1⟩ := hα
      obtain ⟨hql0, hql1⟩ := hql
      obtain ⟨hqh0, hqh1⟩ := hqh
      -- facts on Gamma
      have hG0 : GammaA α 0 = 1 := by
        unfold GammaA; split_ifs <;> simp
      have hbase : ∀ x : ℝ, 0 ≤ x → 1 ≤ 1 + (1 - α) * x := by
        intro x hx
        have : 0 ≤ (1 - α) * x := mul_nonneg (by linarith) hx
        linarith
      have hGpos : ∀ x : ℝ, 0 ≤ x → 0 < GammaA α x := by
        intro x hx
        unfold GammaA
        split_ifs
        · exact Real.exp_pos _
        · exact Real.rpow_pos_of_pos (by linarith [hbase x hx]) _
      have hGmul : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
          GammaA α x * GammaA α y = GammaA α (x + y + (1 - α) * x * y) := by
        intro x y hx hy
        unfold GammaA
        split_ifs with h
        · subst h
          rw [← Real.exp_add]; congr 1; ring
        · rw [← Real.mul_rpow (by linarith [hbase x hx]) (by linarith [hbase y hy])]
          congr 1; ring
      have hGd : ∀ y : ℝ, 0 ≤ y → GammaA α y * (1 + y) ≤ 1 := by
        intro y hy
        unfold GammaA
        split_ifs with h
        · have h1 := Real.add_one_le_exp y
          have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
          have h3 := Real.exp_pos (-y)
          nlinarith
        · have hk : 0 < 1 - α := lt_of_le_of_ne (by linarith) (by intro h'; apply h; linarith)
          have hb := hbase y hy
          have h1 := one_add_mul_self_le_rpow_one_add (s := (1 - α) * y) (by linarith)
            (p := 1 / (1 - α)) (by rw [le_div_iff₀ hk]; linarith)
          have h2 : 1 / (1 - α) * ((1 - α) * y) = y := by field_simp
          rw [h2] at h1
          rw [Real.rpow_neg (by linarith)]
          have h3 : 0 < (1 + (1 - α) * y) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos (by linarith) _
          rw [inv_mul_le_iff₀ h3]; linarith
      have hG1 : ∀ x : ℝ, 0 ≤ x → 1 - x ≤ GammaA α x := by
        intro x hx
        refine (Real.one_sub_le_exp_neg x).trans ?_
        unfold GammaA
        split_ifs with h
        · exact le_rfl
        · have hk : 0 < 1 - α := lt_of_le_of_ne (by linarith) (by intro h'; apply h; linarith)
          have hb := hbase x hx
          have h1 : 1 + (1 - α) * x ≤ Real.exp ((1 - α) * x) := by
            have := Real.add_one_le_exp ((1 - α) * x); linarith
          have h2 := Real.rpow_le_rpow_of_nonpos (z := -(1 / (1 - α))) (by linarith) h1
            (by have : 0 < 1 / (1 - α) := by positivity
                linarith)
          refine le_trans (le_of_eq ?_) h2
          rw [← Real.exp_mul]; congr 1; field_simp
      have hGanti : ∀ x y : ℝ, 0 ≤ x → x ≤ y → GammaA α y ≤ GammaA α x := by
        intro x y hx hxy
        unfold GammaA
        split_ifs with h
        · exact Real.exp_le_exp.2 (by linarith)
        · have hk : 0 < 1 - α := lt_of_le_of_ne (by linarith) (by intro h'; apply h; linarith)
          apply Real.rpow_le_rpow_of_nonpos (by linarith [hbase x hx])
          · have := mul_le_mul_of_nonneg_left hxy hk.le
            linarith
          · have : 0 < 1 / (1 - α) := by positivity
            linarith
      have hGle : ∀ x : ℝ, 0 ≤ x → GammaA α x ≤ 1 := by
        intro x hx; have := hGanti 0 x le_rfl hx; rwa [hG0] at this
      have hInv0 : ∀ q : ℝ, 0 < q → q ≤ 1 → 0 ≤ GammaAInv α q := by
        intro q hq hq1
        unfold GammaAInv
        split_ifs with h
        · have := Real.log_nonpos hq.le hq1; linarith
        · have hk : 0 < 1 - α := lt_of_le_of_ne (by linarith) (by intro h'; apply h; linarith)
          apply div_nonneg _ hk.le
          have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq hq1 (z := -(1 - α)) (by linarith)
          linarith
      have hGI : ∀ q : ℝ, 0 < q → q ≤ 1 → GammaA α (GammaAInv α q) = q := by
        intro q hq hq1
        unfold GammaA GammaAInv
        split_ifs with h
        · rw [neg_neg, Real.exp_log hq]
        · have hk : 0 < 1 - α := lt_of_le_of_ne (by linarith) (by intro h'; apply h; linarith)
          have e : 1 + (1 - α) * ((q ^ (-(1 - α)) - 1) / (1 - α)) = q ^ (-(1 - α)) := by
            field_simp; ring
          rw [e, ← Real.rpow_mul hq.le]
          have e2 : -(1 - α) * -(1 / (1 - α)) = 1 := by field_simp
          rw [e2, Real.rpow_one]
      have hIG : ∀ x : ℝ, 0 ≤ x → GammaAInv α (GammaA α x) = x := by
        intro x hx
        unfold GammaA GammaAInv
        split_ifs with h
        · rw [Real.log_exp, neg_neg]
        · have hk : 0 < 1 - α := lt_of_le_of_ne (by linarith) (by intro h'; apply h; linarith)
          have hb := hbase x hx
          rw [← Real.rpow_mul (by linarith)]
          have e2 : -(1 / (1 - α)) * -(1 - α) = 1 := by field_simp
          rw [e2, Real.rpow_one]; field_simp; ring
      have hIone : GammaAInv α 1 = 0 := by
        have := hIG 0 le_rfl; rwa [hG0] at this
      have hInvPos : ∀ q : ℝ, 0 < q → q < 1 → 0 < GammaAInv α q := by
        intro q hq hq1
        refine lt_of_le_of_ne (hInv0 q hq hq1.le) ?_
        intro h
        have := hGI q hq hq1.le
        rw [← h, hG0] at this; linarith
      have hInvAnti : ∀ q q' : ℝ, 0 < q → q ≤ q' → q' ≤ 1 → GammaAInv α q' ≤ GammaAInv α q := by
        intro q q' hq hqq hq'
        by_contra hcon
        push Not at hcon
        have h1 := hGanti _ _ (hInv0 q hq (hqq.trans hq')) hcon.le
        rw [hGI q hq (hqq.trans hq'), hGI q' (hq.trans_le hqq) hq'] at h1
        have : q = q' := le_antisymm hqq h1
        subst this
        exact lt_irrefl _ hcon
      have hGiff : ∀ u x : ℝ, 0 < u → u ≤ 1 → 0 ≤ x → (x ≤ GammaAInv α u ↔ u ≤ GammaA α x) := by
        intro u x hu hu1 hx
        constructor
        · intro h
          have := hGanti _ _ hx h
          rwa [hGI u hu hu1] at this
        · intro h
          have := hInvAnti u _ hu h (hGle x hx)
          rwa [hIG x hx] at this
      -- ratio monotonicity
      have hG2 : ∀ c c' p r : ℝ, 0 ≤ c' → c' ≤ c → 0 ≤ p → p ≤ r →
          GammaA α (c * r) * GammaA α (c' * p) ≤ GammaA α (c' * r) * GammaA α (c * p) := by
        intro c c' p r hc' hcc hp hpr
        have hk : 0 ≤ 1 - α := by linarith
        have hc : 0 ≤ c := hc'.trans hcc
        have hd : ∀ d : ℝ, 0 ≤ d → GammaA α (d * r) =
            GammaA α (d * p) * GammaA α (d * (r - p) / (1 + (1 - α) * (d * p))) := by
          intro d hd
          have hb := hbase (d * p) (mul_nonneg hd hp)
          rw [hGmul _ _ (mul_nonneg hd hp)
            (div_nonneg (mul_nonneg hd (by linarith)) (by linarith))]
          congr 1
          have : (1 + (1 - α) * (d * p)) ≠ 0 := by linarith
          field_simp
          ring
        rw [hd c hc, hd c' hc']
        have hb := hbase (c * p) (mul_nonneg hc hp)
        have hb' := hbase (c' * p) (mul_nonneg hc' hp)
        have h1 : c' * (r - p) / (1 + (1 - α) * (c' * p)) ≤ c * (r - p) / (1 + (1 - α) * (c * p)) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          have : 0 ≤ (c - c') * (r - p) := mul_nonneg (by linarith) (by linarith)
          nlinarith
        have h2 := hGanti _ _ (div_nonneg (mul_nonneg hc' (by linarith)) (by linarith)) h1
        have h3 := hGpos (c * p) (mul_nonneg hc hp)
        have h4 := hGpos (c' * p) (mul_nonneg hc' hp)
        have h5 := mul_le_mul_of_nonneg_left h2 (mul_nonneg h3.le h4.le)
        nlinarith
      have hG3 : ∀ c p r : ℝ, 0 ≤ c → 0 < p → p ≤ r → 1 ≤ α * c * p →
          r * GammaA α (c * r) ≤ p * GammaA α (c * p) := by
        intro c p r hc hp hpr h1
        have hk : 0 ≤ 1 - α := by linarith
        have hb := hbase (c * p) (mul_nonneg hc hp.le)
        have hy : 0 ≤ c * (r - p) / (1 + (1 - α) * (c * p)) :=
          div_nonneg (mul_nonneg hc (by linarith)) (by linarith)
        have e : GammaA α (c * r) =
            GammaA α (c * p) * GammaA α (c * (r - p) / (1 + (1 - α) * (c * p))) := by
          rw [hGmul _ _ (mul_nonneg hc hp.le) hy]
          congr 1
          have : (1 + (1 - α) * (c * p)) ≠ 0 := by linarith
          field_simp
          ring
        have h2 := hGd _ hy
        have h3 : (r - p) / p ≤ c * (r - p) / (1 + (1 - α) * (c * p)) := by
          rw [div_le_div_iff₀ hp (by linarith)]
          have : 0 ≤ (α * c * p - 1) * (r - p) := mul_nonneg (by linarith) (by linarith)
          nlinarith
        have h4 := hGpos _ hy
        have h5 : r / p ≤ 1 + c * (r - p) / (1 + (1 - α) * (c * p)) := by
          have : r / p = 1 + (r - p) / p := by field_simp; ring
          linarith
        have h6 : GammaA α (c * (r - p) / (1 + (1 - α) * (c * p))) * (r / p) ≤ 1 :=
          (mul_le_mul_of_nonneg_left h5 h4.le).trans h2
        have h7 : GammaA α (c * (r - p) / (1 + (1 - α) * (c * p))) * r ≤ p := by
          rw [← mul_div_assoc, div_le_one hp] at h6; exact h6
        rw [e]
        have h8 := hGpos _ (mul_nonneg hc hp.le)
        nlinarith
      -- general family
      obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ, ∀ s b R v, K s b R v =
          if v < s then 1 else if v ≤ R then GammaA α ((v - s) / b) else 0 := ⟨_, fun _ _ _ _ => rfl⟩
      have hK0 : ∀ s b R v, 0 < b → 0 ≤ K s b R v := by
        intro s b R v hb
        rw [hK]
        split_ifs with h1 h2
        · exact zero_le_one
        · exact (hGpos _ (div_nonneg (by linarith) hb.le)).le
        · exact le_rfl
      have hK1 : ∀ s b R v, 0 < b → K s b R v ≤ 1 := by
        intro s b R v hb
        rw [hK]
        split_ifs with h1 h2
        · exact le_rfl
        · exact (hGle _ (div_nonneg (by linarith) hb.le))
        · exact zero_le_one
      have hInvMeas : Measurable (fun u : ℝ => GammaAInv α u) := by
        unfold GammaAInv
        split_ifs
        · exact Real.measurable_log.neg
        · fun_prop
      have hEx : ∀ s b R : ℝ, 0 ≤ s → 0 < b → s < R → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ν (Set.Iio 0) = 0 ∧ ∀ v : ℝ, 0 ≤ v → sf ν v = K s b R v := by
        intro s b R hs hb hR
        obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, ∀ u, T u = min R (s + b * GammaAInv α u) := ⟨_, fun _ => rfl⟩
        have hTm : Measurable T := by
          have : T = fun u => min R (s + b * GammaAInv α u) := funext hT
          rw [this]
          exact measurable_const.min (measurable_const.add (hInvMeas.const_mul b))
        have hPr : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc 0 1)) :=
          ⟨by simp⟩
        refine ⟨((volume : Measure ℝ).restrict (Set.Ioc 0 1)).map T, ?_, ?_, ?_⟩
        · exact Measure.isProbabilityMeasure_map hTm.aemeasurable
        · rw [Measure.map_apply hTm measurableSet_Iio,
            Measure.restrict_apply (hTm measurableSet_Iio)]
          have : T ⁻¹' Set.Iio 0 ∩ Set.Ioc 0 1 = ∅ := by
            ext u
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio, Set.mem_Ioc,
              Set.mem_empty_iff_false, iff_false, not_and, not_le]
            intro h1 h2
            by_contra h3
            push Not at h3
            have h4 := mul_nonneg hb.le (hInv0 u h2 h3)
            rw [hT, min_lt_iff] at h1
            rcases h1 with h1 | h1 <;> linarith
          rw [this, measure_empty]
        · intro v hv
          unfold sf
          rw [Measure.map_apply hTm measurableSet_Ici,
            Measure.restrict_apply (hTm measurableSet_Ici)]
          have : T ⁻¹' Set.Ici v ∩ Set.Ioc 0 1 = Set.Ioc 0 (K s b R v) := by
            ext u
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, Set.mem_Ioc]
            rw [hT, le_min_iff, hK]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3, h4⟩
              refine ⟨h3, ?_⟩
              split_ifs with h5
              · exact h4
              · rw [← hGiff u _ h3 h4 (div_nonneg (by linarith) hb.le), div_le_iff₀ hb]
                linarith
            · rintro ⟨h3, h4⟩
              split_ifs at h4 with h5 h6
              · have := mul_nonneg hb.le (hInv0 u h3 h4)
                refine ⟨⟨by linarith, by linarith⟩, h3, h4⟩
              · have h0 : 0 ≤ (v - s) / b := div_nonneg (by linarith) hb.le
                have h7 := h4.trans (hGle _ h0)
                rw [← hGiff u _ h3 h7 h0, div_le_iff₀ hb] at h4
                exact ⟨⟨h6, by linarith⟩, h3, h7⟩
              · linarith
          rw [this, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (hK0 s b R v hb)]
      -- every member is in the class
      have hMem : ∀ (μ : Measure ℝ) (s b R : ℝ), 0 ≤ s → 0 < b → s < R → IsProbabilityMeasure μ →
          μ (Set.Iio 0) = 0 → (∀ v : ℝ, 0 ≤ v → sf μ v = K s b R v) → InG μ ∧ IsAlphaSR α μ := by
        intro μ s b R hs hb hR hμ hμ0 hsf
        have hRpos : 0 < R := by linarith
        have hae0 : ∀ᵐ v ∂μ, 0 ≤ v := by
          rw [ae_iff]
          have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
          rw [this]; exact hμ0
        have haeR : ∀ᵐ v ∂μ, v ≤ R := by
          rw [ae_iff]
          have : {a : ℝ | ¬ a ≤ R} = ⋃ n : ℕ, Set.Ici (R + 1 / ((n : ℝ) + 1)) := by
            ext x
            simp only [Set.mem_ofPred_eq, not_le, Set.mem_iUnion, Set.mem_Ici]
            constructor
            · intro hx
              obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
              exact ⟨n, by linarith⟩
            · rintro ⟨n, hn⟩
              have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith
          rw [this, measure_iUnion_null_iff]
          intro n
          have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          have h1 := hsf (R + 1 / ((n : ℝ) + 1)) (by linarith)
          rw [hK, if_neg (by linarith), if_neg (by linarith)] at h1
          unfold sf at h1
          rw [ENNReal.toReal_eq_zero_iff] at h1
          exact h1.resolve_right (measure_ne_top μ _)
        have hint : Integrable (fun v : ℝ => v) μ := by
          refine Integrable.of_bound measurable_id.aestronglyMeasurable R ?_
          filter_upwards [hae0, haeR] with v h1 h2
          simpa [abs_of_nonneg h1] using h2
        refine ⟨⟨hμ, hμ0, hint, ?_⟩, ?_⟩
        · have h1 := mul_meas_ge_le_integral_of_nonneg hae0 hint R
          have h2 := hsf R hRpos.le
          rw [hK, if_neg (by linarith), if_pos le_rfl] at h2
          have h3 := hGpos ((R - s) / b) (div_nonneg (by linarith) hb.le)
          have h4 : μ.real {x : ℝ | R ≤ x} = sf μ R := rfl
          rw [h4, h2] at h1
          exact lt_of_lt_of_le (mul_pos hRpos h3) h1
        · unfold IsAlphaSR
          have hset : {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} = Set.Icc 0 R := by
            ext v
            simp only [Set.mem_ofPred_eq, Set.mem_Icc]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨h1, ?_⟩
              by_contra h3
              push Not at h3
              rw [hsf v h1, hK, if_neg (by linarith), if_neg (by linarith)] at h2
              exact lt_irrefl _ h2
            · rintro ⟨h1, h2⟩
              refine ⟨h1, ?_⟩
              rw [hsf v h1, hK]
              split_ifs with h3
              · exact one_pos
              · exact hGpos _ (div_nonneg (by linarith) hb.le)
          rw [hset]
          have hcx : ConvexOn ℝ (Set.Icc 0 R) (fun v : ℝ => max 0 ((v - s) / b)) := by
            refine ConvexOn.sup (convexOn_const 0 (convex_Icc 0 R)) ?_
            refine ⟨convex_Icc 0 R, ?_⟩
            intro x _ y _ a a' _ _ hab
            have : a' = 1 - a := by linarith
            subst this
            simp only [smul_eq_mul]
            apply le_of_eq
            field_simp
            ring
          refine hcx.congr ?_
          intro v hv
          simp only
          rw [hsf v hv.1, hK]
          split_ifs with h3 h4
          · rw [hIone, max_eq_left]
            exact div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
          · rw [hIG _ (div_nonneg (by linarith) hb.le), max_eq_right]
            exact div_nonneg (by linarith) hb.le
          · exact absurd hv.2 h4
      -- parameters
      have hA := hInvPos ql hql0 hql1
      have hB := hInvPos qh hqh0 hqh1
      obtain ⟨A, hAd⟩ : ∃ A, A = GammaAInv α ql := ⟨_, rfl⟩
      obtain ⟨B, hBd⟩ : ∃ B, B = GammaAInv α qh := ⟨_, rfl⟩
      rw [← hAd] at hA
      rw [← hBd] at hB
      have hr0 : 0 < rLow α w ql := by
        unfold rLow; rw [← hAd]; positivity
      have hr0w : rLow α w ql < w := by
        unfold rLow; rw [← hAd, div_lt_iff₀ (by linarith)]; nlinarith
      have hLow : ∀ r v : ℝ, 0 < r → r < w → Fbar α w ql r v = K r ((w - r) / A) w v := by
        intro r v hr hrw
        unfold Fbar Gbar
        rw [if_pos hrw, hK, hIone, div_one, ← hAd, one_mul, zero_mul, zero_div, hG0]
        congr 3
        have : w - r ≠ 0 := by linarith
        field_simp
      have hHigh : ∀ r v : ℝ, w ≤ r → 0 ≤ v → Fbar α w qh r v = K 0 (w / B) r v := by
        intro r v hr hv
        unfold Fbar Gbar
        rw [if_neg (not_lt.2 hr), hK, if_neg (not_lt.2 hv), if_neg (not_lt.2 hv), div_one, ← hBd,
          one_mul]
        have e : B * (v - 0) / (w - 0) = (v - 0) / (w / B) := by
          rw [sub_zero, sub_zero]; field_simp
        rw [e]
      have hSub : SFamilyI α w ql qh ⊆ FClassI α w ql qh := by
        rintro μ ⟨h1, h2, h3⟩
        rcases h3 with ⟨r, hr, h3⟩ | ⟨r, hr, hr', h3⟩
        · have hrp : 0 < r := hr0.trans_le hr.1
          have hbp : 0 < (w - r) / A := div_pos (by linarith [hr.2]) hA
          have h4 : ∀ v : ℝ, 0 ≤ v → sf μ v = K r ((w - r) / A) w v := fun v hv => by
            rw [h3 v hv, hLow r v hrp hr.2]
          obtain ⟨h5, h6⟩ := hMem μ r _ w hrp.le hbp hr.2 h1 h2 h4
          refine ⟨h5, h6, ?_⟩
          have e : sf μ w = ql := by
            rw [h4 w hw.le, hK, if_neg (by linarith [hr.2]), if_pos le_rfl]
            have : (w - r) / ((w - r) / A) = A := by
              have : w - r ≠ 0 := by linarith [hr.2]
              field_simp
            rw [this, hAd, hGI ql hql0 hql1.le]
          rw [e]; exact ⟨le_rfl, hlh⟩
        · have hbp : 0 < w / B := div_pos hw hB
          have h4 : ∀ v : ℝ, 0 ≤ v → sf μ v = K 0 (w / B) r v := fun v hv => by
            rw [h3 v hv, hHigh r v hr hv]
          obtain ⟨h5, h6⟩ := hMem μ 0 _ r le_rfl hbp (by linarith) h1 h2 h4
          refine ⟨h5, h6, ?_⟩
          have e : sf μ w = qh := by
            rw [h4 w hw.le, hK, if_neg (by linarith), if_pos hr]
            have : (w - 0) / (w / B) = B := by
              field_simp
              ring
            rw [this, hBd, hGI qh hqh0 hqh1.le]
          rw [e]; exact ⟨hlh, le_rfl⟩
      have hLowEx : ∀ r : ℝ, rLow α w ql ≤ r → r < w → ∃ ν ∈ SFamilyI α w ql qh,
          ∀ v : ℝ, 0 ≤ v → sf ν v = K r ((w - r) / A) w v := by
        intro r hr hrw
        have hrp : 0 < r := hr0.trans_le hr
        obtain ⟨ν, h1, h2, h3⟩ := hEx r ((w - r) / A) w hrp.le (div_pos (by linarith) hA) hrw
        refine ⟨ν, ⟨h1, h2, Or.inl ⟨r, ⟨hr, hrw⟩, ?_⟩⟩, h3⟩
        intro v hv
        rw [h3 v hv, hLow r v hrp hrw]
      have hHighEx : ∀ r : ℝ, w ≤ r → α * B * r ≤ w → ∃ ν ∈ SFamilyI α w ql qh,
          ∀ v : ℝ, 0 ≤ v → sf ν v = K 0 (w / B) r v := by
        intro r hr hrw
        obtain ⟨ν, h1, h2, h3⟩ := hEx 0 (w / B) r le_rfl (div_pos hw hB) (by linarith)
        refine ⟨ν, ⟨h1, h2, Or.inr ⟨r, hr, by rw [← hBd]; exact hrw, ?_⟩⟩, h3⟩
        intro v hv
        rw [h3 v hv, hHigh r v hr hv]
      -- analytic facts on laws
      have hsfanti : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → Antitone (sf μ) := by
        intro μ hμ x y hxy
        unfold sf
        exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ici_subset_Ici.2 hxy))
      have hsf0 : ∀ (μ : Measure ℝ) (p : ℝ), 0 ≤ sf μ p := fun μ p => ENNReal.toReal_nonneg
      have hae : ∀ Ψ : Measure ℝ, Ψ (Set.Iio 0) = 0 → ∀ᵐ v ∂Ψ, 0 ≤ v := by
        intro Ψ h
        rw [ae_iff]
        have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
        rw [this]; exact h
      have hMarkov : ∀ μ : Measure ℝ, InG μ → ∀ p : ℝ, p * sf μ p ≤ ∫ v, v ∂μ := by
        intro μ hμ p
        exact mul_meas_ge_le_integral_of_nonneg (hae μ hμ.2.1) hμ.2.2.1 p
      have hBdd : ∀ μ : Measure ℝ, InG μ →
          BddAbove ((fun p : ℝ => p * sf μ p) '' Set.Ici 0) := by
        intro μ hμ
        refine ⟨∫ v, v ∂μ, ?_⟩
        rintro _ ⟨p, _, rfl⟩
        exact hMarkov μ hμ p
      have hInt : ∀ Ψ : Measure ℝ, IsMech Ψ → ∀ μ : Measure ℝ, InG μ →
          Integrable (fun p => p * sf μ p) Ψ := by
        intro Ψ hΨ μ hμ
        have := hΨ.1
        refine Integrable.of_bound
          (measurable_id.mul (hsfanti μ hμ.1).measurable).aestronglyMeasurable (∫ v, v ∂μ) ?_
        filter_upwards [hae Ψ hΨ.2] with p hp
        have h0 : 0 ≤ p * sf μ p := mul_nonneg hp (hsf0 μ p)
        rw [Real.norm_of_nonneg h0]
        exact hMarkov μ hμ p
      have hInt0 : ∀ Ψ : Measure ℝ, IsMech Ψ → ∀ μ : Measure ℝ, 0 ≤ ∫ p, p * sf μ p ∂Ψ := by
        intro Ψ hΨ μ
        apply integral_nonneg_of_ae
        filter_upwards [hae Ψ hΨ.2] with p hp
        exact mul_nonneg hp (hsf0 μ p)
      have hopt0 : ∀ μ : Measure ℝ, 0 ≤ opt μ := by
        intro μ
        apply Real.sSup_nonneg
        rintro _ ⟨p, hp, rfl⟩
        exact mul_nonneg hp (hsf0 μ p)
      have hrat0 : ∀ Ψ : Measure ℝ, IsMech Ψ → ∀ μ : Measure ℝ, 0 ≤ ratio Ψ μ := by
        intro Ψ hΨ μ
        exact div_nonneg (hInt0 Ψ hΨ μ) (hopt0 μ)
      have hbelow : ∀ Ψ : Measure ℝ, IsMech Ψ → ∀ S : Set (Measure ℝ),
          BddBelow (ratio Ψ '' S) := by
        intro Ψ hΨ S
        refine ⟨0, ?_⟩
        rintro _ ⟨μ, _, rfl⟩
        exact hrat0 Ψ hΨ μ
      -- main comparison
      have hComp : ∀ Ψ : Measure ℝ, IsMech Ψ → ∀ μ : Measure ℝ, InG μ →
          ∀ ν ∈ SFamilyI α w ql qh, ∀ t C D : ℝ, 0 ≤ t → 0 < D → 0 ≤ C → D ≤ t * sf ν t →
          (∀ p : ℝ, 0 ≤ p → C * sf ν p ≤ sf μ p * D) →
          sInf (ratio Ψ '' SFamilyI α w ql qh) * C ≤ ∫ p, p * sf μ p ∂Ψ := by
        intro Ψ hΨ μ hμ ν hν t C D ht hD hC hDt hp
        have hνG := (hSub hν).1
        have h1 : sInf (ratio Ψ '' SFamilyI α w ql qh) ≤ ratio Ψ ν :=
          csInf_le (hbelow Ψ hΨ _) ⟨ν, hν, rfl⟩
        have h2 : D ≤ opt ν := hDt.trans (le_csSup (hBdd ν hνG) ⟨t, ht, rfl⟩)
        have h3 : ratio Ψ ν ≤ (∫ p, p * sf ν p ∂Ψ) / D :=
          div_le_div_of_nonneg_left (hInt0 Ψ hΨ ν) hD h2
        have h4 : C * ∫ p, p * sf ν p ∂Ψ ≤ (∫ p, p * sf μ p ∂Ψ) * D := by
          rw [← integral_const_mul, ← integral_mul_const]
          apply integral_mono_ae ((hInt Ψ hΨ ν hνG).const_mul C) ((hInt Ψ hΨ μ hμ).mul_const D)
          filter_upwards [hae Ψ hΨ.2] with p hp0
          have := mul_le_mul_of_nonneg_left (hp p hp0) hp0
          calc C * (p * sf ν p) = p * (C * sf ν p) := by ring
            _ ≤ p * (sf μ p * D) := this
            _ = p * sf μ p * D := by ring
        calc sInf (ratio Ψ '' SFamilyI α w ql qh) * C
            ≤ (∫ p, p * sf ν p ∂Ψ) / D * C := mul_le_mul_of_nonneg_right (h1.trans h3) hC
          _ = (C * ∫ p, p * sf ν p ∂Ψ) / D := by ring
          _ ≤ ∫ p, p * sf μ p ∂Ψ := by rw [div_le_iff₀ hD]; exact h4
      have hMain : ∀ Ψ : Measure ℝ, IsMech Ψ → ∀ μ ∈ FClassI α w ql qh, ∀ r : ℝ, 0 ≤ r →
          sInf (ratio Ψ '' SFamilyI α w ql qh) * (r * sf μ r) ≤ ∫ p, p * sf μ p ∂Ψ := by
        intro Ψ hΨ μ hμ r hr
        obtain ⟨hμG, hSR, hqw⟩ := hμ
        have := hμG.1
        have hanti := hsfanti μ hμG.1
        have hsfle : ∀ p, sf μ p ≤ 1 := by
          intro p
          unfold sf
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        have hsfz : sf μ 0 = 1 := by
          have h1 : μ (Set.Ici 0) = 1 := by
            have : Set.Ici (0:ℝ) = (Set.Iio 0)ᶜ := by ext; simp
            rw [this, prob_compl_eq_one_iff measurableSet_Iio]
            exact hμG.2.1
          unfold sf; rw [h1]; simp
        rcases hr.eq_or_lt with hr0' | hrpos
        · rw [← hr0', zero_mul, mul_zero]; exact hInt0 Ψ hΨ μ
        rcases (hsf0 μ r).eq_or_lt with hz | hHr
        · rw [← hz, mul_zero, mul_zero]; exact hInt0 Ψ hΨ μ
        have hHw : 0 < sf μ w := hql0.trans_le hqw.1
        -- convexity
        have hcv : ∀ x y z : ℝ, 0 ≤ x → x ≤ z → z ≤ y → x < y → 0 < sf μ y →
            GammaAInv α (sf μ z) ≤ GammaAInv α (sf μ x) +
              (GammaAInv α (sf μ y) - GammaAInv α (sf μ x)) * ((z - x) / (y - x)) := by
          intro x y z hx hxz hzy hxy hy
          have hyx : 0 < y - x := by linarith
          have hxm : x ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨hx, hy.trans_le (hanti hxy.le)⟩
          have hym : y ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨by linarith, hy⟩
          have ha : 0 ≤ (y - z) / (y - x) := div_nonneg (by linarith) hyx.le
          have hb : 0 ≤ (z - x) / (y - x) := div_nonneg (by linarith) hyx.le
          have hab : (y - z) / (y - x) + (z - x) / (y - x) = 1 := by field_simp; ring
          have h := hSR.2 hxm hym ha hb hab
          simp only [smul_eq_mul] at h
          have e1 : (y - z) / (y - x) * x + (z - x) / (y - x) * y = z := by field_simp; ring
          have e2 : (y - z) / (y - x) = 1 - (z - x) / (y - x) := by field_simp; ring
          rw [e1, e2] at h
          linarith
        have hφ0 : ∀ x, 0 < sf μ x → 0 ≤ GammaAInv α (sf μ x) := fun x hx => hInv0 _ hx (hsfle x)
        have hφG : ∀ x, 0 < sf μ x → GammaA α (GammaAInv α (sf μ x)) = sf μ x :=
          fun x hx => hGI _ hx (hsfle x)
        -- low comparison
        have hlowcmp : ∀ r p : ℝ, 0 ≤ r → r < w → 0 ≤ p →
            sf μ r * K r ((w - r) / A) w p ≤ sf μ p := by
          intro r p hr hrw hp
          rw [hK]
          split_ifs with h1 h2
          · rw [mul_one]; exact hanti h1.le
          · push Not at h1
            have hwr : 0 < w - r := by linarith
            have hHr : 0 < sf μ r := hHw.trans_le (hanti hrw.le)
            have hHp : 0 < sf μ p := hHw.trans_le (hanti h2)
            have h3 := hcv r w p hr h1 h2 hrw hHw
            have hf0 := hφ0 r hHr
            have hfw : GammaAInv α (sf μ w) ≤ A := by
              rw [hAd]; exact hInvAnti ql _ hql0 hqw.1 (hsfle w)
            have hfrw : GammaAInv α (sf μ r) ≤ GammaAInv α (sf μ w) :=
              hInvAnti _ _ hHw (hanti hrw.le) (hsfle r)
            have ht : 0 ≤ (p - r) / (w - r) := div_nonneg (by linarith) hwr.le
            have e : (p - r) / ((w - r) / A) = A * ((p - r) / (w - r)) := by field_simp
            have hAt : 0 ≤ A * ((p - r) / (w - r)) := mul_nonneg hA.le ht
            rw [e]
            calc sf μ r * GammaA α (A * ((p - r) / (w - r)))
                = GammaA α (GammaAInv α (sf μ r)) * GammaA α (A * ((p - r) / (w - r))) := by
                  rw [hφG r hHr]
              _ = GammaA α (GammaAInv α (sf μ r) + A * ((p - r) / (w - r)) +
                    (1 - α) * GammaAInv α (sf μ r) * (A * ((p - r) / (w - r)))) :=
                  hGmul _ _ hf0 hAt
              _ ≤ GammaA α (GammaAInv α (sf μ p)) := by
                  apply hGanti _ _ (hφ0 p hHp)
                  have h4 : 0 ≤ (1 - α) * GammaAInv α (sf μ r) * (A * ((p - r) / (w - r))) :=
                    mul_nonneg (mul_nonneg (by linarith) hf0) hAt
                  have h5 : (GammaAInv α (sf μ w) - GammaAInv α (sf μ r)) * ((p - r) / (w - r)) ≤
                      A * ((p - r) / (w - r)) := mul_le_mul_of_nonneg_right (by linarith) ht
                  linarith
              _ = sf μ p := hφG p hHp
          · rw [mul_zero]; exact hsf0 μ p
        have hKs : ∀ s R b : ℝ, s < R → K s b R s = 1 := by
          intro s R b h
          rw [hK, if_neg (lt_irrefl s), if_pos h.le, sub_self, zero_div, hG0]
        rcases lt_or_ge r w with hrw | hrw
        · rcases le_or_gt (rLow α w ql) r with hrl | hrl
          · obtain ⟨ν, hν, hνs⟩ := hLowEx r hrl hrw
            refine hComp Ψ hΨ μ hμG ν hν r _ r hr hrpos (mul_nonneg hr hHr.le) ?_ ?_
            · rw [hνs r hr, hKs r w _ hrw, mul_one]
            · intro p hp
              rw [hνs p hp]
              have := mul_le_mul_of_nonneg_left (hlowcmp r p hr hrw hp) hr
              linarith
          · obtain ⟨ν, hν, hνs⟩ := hLowEx (rLow α w ql) le_rfl hr0w
            obtain ⟨r0, hr0d⟩ : ∃ r0, r0 = rLow α w ql := ⟨_, rfl⟩
            rw [← hr0d] at hνs hrl hr0 hr0w
            have key : r * sf μ r ≤ r0 * sf μ r0 := by
              have h1 := hlowcmp r r0 hr hrw hr0.le
              rw [hK, if_neg (by linarith), if_pos hr0w.le] at h1
              have hwr : 0 < w - r := by linarith
              have hx0 : 0 ≤ (r0 - r) / ((w - r) / A) :=
                div_nonneg (by linarith) (div_pos hwr hA).le
              have h2 := hG1 _ hx0
              have hA' : A * r0 = w - r0 := by
                rw [hr0d]; unfold rLow; rw [← hAd]; field_simp; ring
              have h3 : (r0 - r) / ((w - r) / A) ≤ 1 - r / r0 := by
                have e1 : (r0 - r) / ((w - r) / A) = A * (r0 - r) / (w - r) := by field_simp
                have e2 : 1 - r / r0 = (r0 - r) / r0 := by field_simp
                rw [e1, e2, div_le_div_iff₀ hwr hr0]
                have : A * (r0 - r) * r0 = (w - r0) * (r0 - r) := by rw [← hA']; ring
                rw [this]
                nlinarith
              have h4 : r / r0 ≤ GammaA α ((r0 - r) / ((w - r) / A)) := by linarith
              have h5 : sf μ r * (r / r0) ≤ sf μ r0 :=
                (mul_le_mul_of_nonneg_left h4 hHr.le).trans h1
              have h6 : sf μ r * (r / r0) = (r * sf μ r) / r0 := by ring
              rw [h6, div_le_iff₀ hr0] at h5
              linarith
            refine hComp Ψ hΨ μ hμG ν hν r0 _ r0 hr0.le hr0 (mul_nonneg hr hHr.le) ?_ ?_
            · rw [hνs r0 hr0.le, hKs r0 w _ hr0w, mul_one]
            · intro p hp
              rw [hνs p hp]
              have h1 := mul_le_mul_of_nonneg_left (hlowcmp r0 p hr0.le hr0w hp) hr0.le
              have h2 := mul_le_mul_of_nonneg_right key
                (hK0 r0 ((w - r0) / A) w p (div_pos (by linarith) hA))
              linarith
        · -- high prices
          obtain ⟨c, hcd⟩ : ∃ c, c = GammaAInv α (sf μ r) / r := ⟨_, rfl⟩
          have hc0 : 0 ≤ c := by rw [hcd]; exact div_nonneg (hφ0 r hHr) hr
          have hcr : c * r = GammaAInv α (sf μ r) := by rw [hcd]; field_simp
          have hGr : GammaA α (c * r) = sf μ r := by rw [hcr, hφG r hHr]
          have hφle : ∀ p : ℝ, 0 ≤ p → p ≤ r → GammaAInv α (sf μ p) ≤ c * p := by
            intro p hp hpr
            have h := hcv 0 r p le_rfl hp hpr hrpos hHr
            rw [hsfz, hIone, ← hcr] at h
            have e : 0 + (c * r - 0) * ((p - 0) / (r - 0)) = c * p := by
              field_simp
              ring
            rw [e] at h; exact h
          have hHge : ∀ p : ℝ, 0 ≤ p → p ≤ r → GammaA α (c * p) ≤ sf μ p := by
            intro p hp hpr
            have hHp : 0 < sf μ p := hHr.trans_le (hanti hpr)
            have := hGanti _ _ (hφ0 p hHp) (hφle p hp hpr)
            rwa [hφG p hHp] at this
          have hcc : B / w ≤ c := by
            rw [div_le_iff₀ hw]
            refine le_trans ?_ (hφle w hw.le hrw)
            rw [hBd]; exact hInvAnti _ _ hHw hqw.2 hqh1.le
          have hc' : 0 < B / w := div_pos hB hw
          -- pointwise
          have hpt : ∀ p : ℝ, 0 ≤ p → p ≤ r →
              sf μ r * GammaA α (B / w * p) ≤ GammaA α (B / w * r) * sf μ p := by
            intro p hp hpr
            rw [← hGr]
            refine (hG2 c (B / w) p r hc'.le hcc hp hpr).trans ?_
            exact mul_le_mul_of_nonneg_left (hHge p hp hpr) (hGpos _ (mul_nonneg hc'.le hr)).le
          have hKh : ∀ R p : ℝ, 0 ≤ p → p ≤ R → K 0 (w / B) R p = GammaA α (B / w * p) := by
            intro R p hp hpR
            rw [hK, if_neg (by linarith), if_pos hpR]
            congr 1
            field_simp
            ring
          rcases le_or_gt (α * B * r) w with h1 | h1
          · obtain ⟨ν, hν, hνs⟩ := hHighEx r hrw h1
            refine hComp Ψ hΨ μ hμG ν hν r _ (r * GammaA α (B / w * r)) hr
              (mul_pos hrpos (hGpos _ (mul_nonneg hc'.le hr))) (mul_nonneg hr hHr.le) ?_ ?_
            · rw [hνs r hr, hKh r r hr le_rfl]
            · intro p hp
              rw [hνs p hp]
              rcases le_or_gt p r with hpr | hpr
              · rw [hKh r p hp hpr]
                have := mul_le_mul_of_nonneg_left (hpt p hp hpr) hr
                linarith
              · rw [hK, if_neg (by linarith), if_neg (by linarith), mul_zero]
                exact mul_nonneg (hsf0 μ p) (mul_nonneg hr (hGpos _ (mul_nonneg hc'.le hr)).le)
          · have hαB : 0 < α * B := by
              by_contra hcon
              push Not at hcon
              have := mul_nonpos_of_nonpos_of_nonneg hcon hr
              linarith
            rcases le_or_gt (α * B * w) w with h2 | h2
            · obtain ⟨r', hr'⟩ : ∃ r', r' = w / (α * B) := ⟨_, rfl⟩
              have e1 : α * B * r' = w := by
                rw [hr']; exact mul_div_cancel₀ _ hαB.ne'
              have hr'w : w ≤ r' := by
                rw [hr', le_div_iff₀ hαB]; linarith
              have hr'r : r' ≤ r := by
                rw [hr', div_le_iff₀ hαB]; linarith
              have hr'p : 0 < r' := hw.trans_le hr'w
              have e2 : 1 ≤ α * (B / w) * r' := by
                have : α * (B / w) * r' = (α * B * r') / w := by ring
                rw [this, e1, div_self hw.ne']
              have h3 := hG3 (B / w) r' r hc'.le hr'p hr'r e2
              obtain ⟨ν, hν, hνs⟩ := hHighEx r' hr'w e1.le
              refine hComp Ψ hΨ μ hμG ν hν r' _ (r' * GammaA α (B / w * r')) hr'p.le
                (mul_pos hr'p (hGpos _ (mul_nonneg hc'.le hr'p.le))) (mul_nonneg hr hHr.le) ?_ ?_
              · rw [hνs r' hr'p.le, hKh r' r' hr'p.le le_rfl]
              · intro p hp
                rw [hνs p hp]
                rcases le_or_gt p r' with hpr | hpr
                · rw [hKh r' p hp hpr]
                  have h4 := mul_le_mul_of_nonneg_left (hpt p hp (hpr.trans hr'r)) hr
                  have h5 := mul_le_mul_of_nonneg_right h3 (hsf0 μ p)
                  linarith
                · rw [hK, if_neg (by linarith), if_neg (by linarith), mul_zero]
                  exact mul_nonneg (hsf0 μ p)
                    (mul_nonneg hr'p.le (hGpos _ (mul_nonneg hc'.le hr'p.le)).le)
            · -- degenerate case
              have e2 : 1 ≤ α * c * w := by
                have h3 : α * (B / w) * w ≤ α * c * w :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcc hα0) hw.le
                have h4 : α * (B / w) * w = α * B := by field_simp
                have h5 : 1 < α * B := by
                  by_contra hcon
                  push Not at hcon
                  have := mul_le_mul_of_nonneg_right hcon hw.le
                  linarith
                linarith
              have h3 := hG3 c w r hc0 hw hrw e2
              rw [hGr] at h3
              have h4 : r * sf μ r ≤ w * sf μ w :=
                h3.trans (mul_le_mul_of_nonneg_left (hHge w hw.le hrw) hw.le)
              have h5 : ∀ ρ : ℝ, rLow α w ql ≤ ρ → ρ < w →
                  sInf (ratio Ψ '' SFamilyI α w ql qh) * (ρ / w * (r * sf μ r)) ≤
                    ∫ p, p * sf μ p ∂Ψ := by
                intro ρ hρ hρw
                have hρ0 : 0 < ρ := hr0.trans_le hρ
                obtain ⟨ν, hν, hνs⟩ := hLowEx ρ hρ hρw
                refine hComp Ψ hΨ μ hμG ν hν ρ _ ρ hρ0.le hρ0
                  (mul_nonneg (div_nonneg hρ0.le hw.le) (mul_nonneg hr hHr.le)) ?_ ?_
                · rw [hνs ρ hρ0.le, hKs ρ w _ hρw, mul_one]
                · intro p hp
                  rw [hνs p hp]
                  have hb : 0 < (w - ρ) / A := div_pos (by linarith) hA
                  have hC : 0 ≤ ρ / w * (r * sf μ r) :=
                    mul_nonneg (div_nonneg hρ0.le hw.le) (mul_nonneg hr hHr.le)
                  rcases le_or_gt p w with hpw | hpw
                  · have h6 : ρ / w * (r * sf μ r) ≤ ρ / w * (w * sf μ w) :=
                      mul_le_mul_of_nonneg_left h4 (div_nonneg hρ0.le hw.le)
                    have h7 : ρ / w * (w * sf μ w) = ρ * sf μ w := by field_simp
                    have h8 := mul_le_mul_of_nonneg_left (hK1 ρ ((w - ρ) / A) w p hb) hC
                    have h9 := mul_le_mul_of_nonneg_left (hanti hpw) hρ0.le
                    linarith
                  · rw [hK, if_neg (by linarith), if_neg (by linarith), mul_zero]
                    exact mul_nonneg (hsf0 μ p) hρ0.le
              have hlim : Filter.Tendsto (fun ρ : ℝ =>
                  sInf (ratio Ψ '' SFamilyI α w ql qh) * (ρ / w * (r * sf μ r)))
                  (nhdsWithin w (Set.Iio w))
                  (nhds (sInf (ratio Ψ '' SFamilyI α w ql qh) * (w / w * (r * sf μ r)))) := by
                apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
                apply Continuous.tendsto
                fun_prop
              rw [div_self hw.ne', one_mul] at hlim
              refine le_of_tendsto hlim ?_
              filter_upwards [Ioo_mem_nhdsLT hr0w] with ρ hρ
              exact h5 ρ hρ.1.le hρ.2
      -- conclusion
      have hSne : (SFamilyI α w ql qh).Nonempty := by
        obtain ⟨ν, hν, _⟩ := hLowEx _ le_rfl hr0w
        exact ⟨ν, hν⟩
      have hEq : ∀ Ψ ∈ P', sInf (ratio Ψ '' FClassI α w ql qh) =
          sInf (ratio Ψ '' SFamilyI α w ql qh) := by
        intro Ψ hΨP
        have hΨ : IsMech Ψ := hP hΨP
        apply le_antisymm
        · exact csInf_le_csInf (hbelow Ψ hΨ _) (hSne.image _) (Set.image_mono hSub)
        · apply le_csInf ((hSne.mono hSub).image _)
          rintro _ ⟨μ, hμ, rfl⟩
          have hopt : 0 < opt μ := by
            have h1 : w * sf μ w ≤ opt μ := le_csSup (hBdd μ hμ.1) ⟨w, hw.le, rfl⟩
            have h2 : 0 < w * sf μ w := mul_pos hw (hql0.trans_le hμ.2.2.1)
            linarith
          have hm0 : 0 ≤ sInf (ratio Ψ '' SFamilyI α w ql qh) := by
            apply Real.sInf_nonneg
            rintro _ ⟨ν, _, rfl⟩
            exact hrat0 Ψ hΨ ν
          unfold ratio at *
          rw [le_div_iff₀ hopt]
          rcases hm0.eq_or_lt with hm | hm
          · rw [← hm, zero_mul]; exact hInt0 Ψ hΨ μ
          · rw [mul_comm, ← le_div_iff₀ hm]
            apply csSup_le (Set.Nonempty.image _ ⟨0, Set.self_mem_Ici⟩)
            rintro _ ⟨r, hr, rfl⟩
            rw [le_div_iff₀ hm, mul_comm]
            exact hMain Ψ hΨ μ hμ r hr
      unfold maximin
      rw [Set.image_congr hEq]
