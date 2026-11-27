-- Prove2me | solution 1 for SPPRevenue.SingleUnit.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:19.696649+00:00
-- url     : https://prove2.me/submissions/fe03a9b5-0c8f-4eee-996a-1e097bf6531f

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiProgram

open SPPRevenue
open SPPRevenue.SingleUnit
open SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (H : ℕ) (hH : 1 < H) :
    (∃! T : ℝ, 1 / (H : ℝ) < T ∧ multiRootEq H T) ∧
      ∀ T : ℝ, 1 / (H : ℝ) < T → multiRootEq H T →
        IsFactorProgram (frMultiValues H) ∧
          frMulti H = ENNReal.ofReal (1 + Real.log ((H : ℝ) * T)) := by
            -- partial exponential sums
            have hE : ∀ k : ℕ, ∀ x : ℝ, HasDerivAt
                (fun x : ℝ => ∑ i ∈ Finset.range (k+1), x ^ i / (i.factorial : ℝ))
                (∑ i ∈ Finset.range k, x ^ i / (i.factorial : ℝ)) x := by
              intro k
              induction k with
              | zero =>
                intro x
                simpa using hasDerivAt_const x (1:ℝ)
              | succ k ih =>
                intro x
                have h1 := (ih x).add ((hasDerivAt_pow (k+1) x).div_const ((k+1).factorial : ℝ))
                have heq : (fun x : ℝ => ∑ i ∈ Finset.range (k+1+1), x ^ i / (i.factorial : ℝ)) =
                    fun x => (∑ i ∈ Finset.range (k+1), x ^ i / (i.factorial : ℝ)) +
                      x ^ (k+1) / ((k+1).factorial : ℝ) := by
                  funext y; rw [Finset.sum_range_succ]
                rw [heq]
                refine h1.congr_deriv ?_
                rw [Finset.sum_range_succ, Nat.factorial_succ]; push_cast
                field_simp
            have hSeq : ∀ x : ℝ, ∑ i ∈ Finset.range H, ((H : ℝ) - i) * x ^ i / (i.factorial : ℝ) =
                ∑ j ∈ Finset.range H, ∑ i ∈ Finset.range (j+1), x ^ i / (i.factorial : ℝ) := by
              intro x
              clear hH
              induction H with
              | zero => simp
              | succ k ih =>
                rw [Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range (j+1), x ^ i / (i.factorial : ℝ)) k, ← ih]
                push_cast
                have : ∑ i ∈ Finset.range k, ((k:ℝ) + 1 - i) * x ^ i / (i.factorial : ℝ) =
                    ∑ i ∈ Finset.range k, ((k:ℝ) - i) * x ^ i / (i.factorial : ℝ) +
                    ∑ i ∈ Finset.range k, x ^ i / (i.factorial : ℝ) := by
                  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
                rw [Finset.sum_range_succ, this, Finset.sum_range_succ (fun i => x ^ i / (i.factorial : ℝ)) k]
                ring
            have hEsum : ∀ x : ℝ, ∑ j ∈ Finset.range H, ∑ i ∈ Finset.range (j+1), x ^ i / (i.factorial : ℝ) -
                ∑ j ∈ Finset.range H, ∑ i ∈ Finset.range j, x ^ i / (i.factorial : ℝ) =
                ∑ i ∈ Finset.range H, x ^ i / (i.factorial : ℝ) := by
              intro x
              rw [← Finset.sum_sub_distrib,
                Finset.sum_range_sub (fun j => ∑ i ∈ Finset.range j, x ^ i / (i.factorial : ℝ)) H]
              simp
            have hfd : ∀ x : ℝ, HasDerivAt (fH H)
                (Real.exp (-x) * ∑ i ∈ Finset.range H, x ^ i / (i.factorial : ℝ)) x := by
              intro x
              have hS : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range H, ∑ i ∈ Finset.range (j+1),
                  x ^ i / (i.factorial : ℝ))
                  (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range j, x ^ i / (i.factorial : ℝ)) x :=
                HasDerivAt.fun_sum (fun j _ => hE j x)
              have hfe : fH H = fun x => (H:ℝ) - Real.exp (-x) * ∑ j ∈ Finset.range H,
                  ∑ i ∈ Finset.range (j+1), x ^ i / (i.factorial : ℝ) := by
                funext y; unfold fH; rw [hSeq]
              rw [hfe]
              have h2 := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul hS
              have h3 := (hasDerivAt_const x (H:ℝ)).sub h2
              refine h3.congr_deriv ?_
              rw [← hEsum x]; simp; ring
            obtain ⟨n, hn⟩ : ∃ n, H = n + 1 := ⟨H - 1, by omega⟩
            have hpd : ∀ x : ℝ, HasDerivAt
                (fun x : ℝ => Real.exp (-x) * ∑ i ∈ Finset.range H, x ^ i / (i.factorial : ℝ))
                (-(Real.exp (-x) * (x ^ n / (n.factorial : ℝ)))) x := by
              intro x
              rw [hn]
              have h2 := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul (hE n x)
              refine h2.congr_deriv ?_
              rw [Finset.sum_range_succ]; simp; ring
            have hEge : ∀ x : ℝ, 0 ≤ x → 1 ≤ ∑ i ∈ Finset.range H, x ^ i / (i.factorial : ℝ) := by
              intro x hx
              have := Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ))
                (fun i _ => by positivity) (Finset.mem_range.2 (by omega : 0 < H))
              simpa using this
            have hcont : Continuous (fH H) := by unfold fH; fun_prop
            have hf0 : fH H 0 = 0 := by
              unfold fH; rw [hn, Finset.sum_range_succ']; simp
            have hderiv : deriv (fH H) =
                fun x => Real.exp (-x) * ∑ i ∈ Finset.range H, x ^ i / (i.factorial : ℝ) :=
              funext (fun x => (hfd x).deriv)
            have hmono : StrictMonoOn (fH H) (Set.Ici 0) := by
              apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn
              intro x hx
              rw [interior_Ici] at hx
              rw [hderiv]
              have := hEge x (le_of_lt hx)
              positivity
            have hfpos : ∀ x : ℝ, 0 < x → 0 < fH H x := by
              intro x hx
              have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
              rwa [hf0] at this
            have hfnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ fH H x := by
              intro x hx
              rcases hx.lt_or_eq with h | h
              · exact (hfpos x h).le
              · rw [← h, hf0]
            have hconc : ConcaveOn ℝ (Set.Ici 0) (fH H) := by
              apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hcont.continuousOn
                (fun x _ => (hfd x).differentiableAt.differentiableWithinAt)
              rw [interior_Ici, hderiv]
              apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) (by fun_prop)
                (fun x _ => (hpd x).differentiableAt.differentiableWithinAt)
              intro x hx
              rw [interior_Ioi] at hx
              rw [(hpd x).deriv]
              have : 0 ≤ x := le_of_lt hx
              have : 0 ≤ Real.exp (-x) * (x ^ n / (n.factorial : ℝ)) := by positivity
              linarith
            have hkey : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a * fH H b ≤ b * fH H a := by
              intro a b ha hab
              rcases (ha.trans hab).lt_or_eq with hb | hb
              · have h := hconc.2 (Set.mem_Ici.2 (ha.trans hab)) (Set.mem_Ici.2 le_rfl)
                  (div_nonneg ha hb.le) (sub_nonneg.2 ((div_le_one hb).2 hab)) (by ring)
                simp only [smul_eq_mul, mul_zero, add_zero, hf0] at h
                rw [div_mul_cancel₀ _ hb.ne'] at h
                have := mul_le_mul_of_nonneg_left h hb.le
                rw [← mul_assoc, mul_div_cancel₀ _ hb.ne'] at this
                linarith
              · have : a = 0 := le_antisymm (hb ▸ hab) ha
                subst this; rw [← hb]
            have htel : ∀ (m : ℕ) (y : ℝ), ∑ i ∈ Finset.range m, (y - i) * y ^ i / (i.factorial : ℝ) =
                m * y ^ m / (m.factorial : ℝ) := by
              intro m y
              have : ∀ i ∈ Finset.range m, (y - i) * y ^ i / (i.factorial : ℝ) =
                  ((i+1:ℕ):ℝ) * y ^ (i+1) / ((i+1).factorial : ℝ) - (i:ℝ) * y ^ i / (i.factorial : ℝ) := by
                intro i _
                rw [Nat.factorial_succ]; push_cast
                field_simp
                ring
              rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i => (i:ℝ) * y ^ i / (i.factorial : ℝ))]
              simp
            set c0 : ℝ := (H : ℝ) ^ H / ((H.factorial : ℝ) * Real.exp H) with hc0
            have hfH : fH H H = H * (1 - c0) := by
              unfold fH; rw [htel, hc0, Real.exp_neg]
              field_simp
            have hHpos : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
            have hiH : (0:ℝ) < 1 / (H:ℝ) := by positivity
            have hc0pos : 0 < c0 := by rw [hc0]; positivity
            have hc0lt : c0 < 1 := by
              have := hfpos H hHpos
              rw [hfH] at this
              nlinarith
            have hroot : ∀ T : ℝ, multiRootEq H T ↔ ∫ τ in (1/(H:ℝ))..T, fH H (1/τ) = c0 := by
              intro T
              unfold multiRootEq
              have : (fun τ : ℝ => ((H : ℝ) - Real.exp (-(1 / τ)) *
                  ∑ i ∈ Finset.range H, ((H : ℝ) - i) / (τ ^ i * (i.factorial : ℝ)))) =
                  fun τ => fH H (1/τ) := by
                funext τ; unfold fH
                congr 2
                apply Finset.sum_congr rfl; intro i _
                rw [one_div_pow, mul_one_div, div_div]
              rw [this]
            have hφc : ContinuousOn (fun τ : ℝ => fH H (1/τ)) (Set.Ioi 0) :=
              hcont.comp_continuousOn (continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx))
            have hφi : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (fun τ : ℝ => fH H (1/τ)) volume a b := by
              intro a b ha hb
              apply ContinuousOn.intervalIntegrable
              apply hφc.mono
              intro x hx
              rcases Set.mem_uIcc.1 hx with h | h
              · exact lt_of_lt_of_le ha h.1
              · exact lt_of_lt_of_le hb h.1
            have hφpos : ∀ τ : ℝ, 0 < τ → 0 < fH H (1/τ) := fun τ hτ => hfpos _ (by positivity)
            have hφlb : ∀ τ : ℝ, 1/(H:ℝ) ≤ τ → (1 - c0) * (1/τ) ≤ fH H (1/τ) := by
              intro τ hτ
              have hτp : 0 < τ := lt_of_lt_of_le hiH hτ
              have h1 : 1/τ ≤ H := by
                rw [div_le_iff₀ hτp]; rw [div_le_iff₀ hHpos] at hτ; linarith
              have := hkey (1/τ) H (by positivity) h1
              rw [hfH] at this
              have h2 : (1/τ) * (H * (1 - c0)) = H * ((1 - c0) * (1/τ)) := by ring
              rw [h2] at this
              exact le_of_mul_le_mul_left this hHpos
            have huniq : ∀ T1 T2 : ℝ, 1/(H:ℝ) < T1 → T1 < T2 →
                ∫ τ in (1/(H:ℝ))..T1, fH H (1/τ) < ∫ τ in (1/(H:ℝ))..T2, fH H (1/τ) := by
              intro T1 T2 h1 h2
              have hT1 : 0 < T1 := hiH.trans h1
              have := intervalIntegral.integral_interval_sub_left (hφi _ _ hiH (hT1.trans h2)) (hφi _ _ hiH hT1)
              have hp := intervalIntegral.intervalIntegral_pos_of_pos_on (hφi _ _ hT1 (hT1.trans h2))
                (fun x hx => hφpos x (hT1.trans hx.1)) h2
              linarith
            have hexists : ∃ T : ℝ, 1 / (H : ℝ) < T ∧ multiRootEq H T := by
              set T1 : ℝ := Real.exp (c0 / (1 - c0)) / H with hT1
              have hT1ge : 1/(H:ℝ) ≤ T1 := by
                rw [hT1]; apply div_le_div_of_nonneg_right _ hHpos.le
                exact Real.one_le_exp (by apply div_nonneg hc0pos.le; linarith)
              have hT1pos : 0 < T1 := lt_of_lt_of_le hiH hT1ge
              have hbig : c0 ≤ ∫ τ in (1/(H:ℝ))..T1, fH H (1/τ) := by
                have hm := intervalIntegral.integral_mono_on hT1ge
                  (by
                    apply ContinuousOn.intervalIntegrable
                    apply ContinuousOn.mul continuousOn_const
                    apply continuousOn_const.div continuousOn_id
                    intro x hx
                    rw [Set.uIcc_of_le hT1ge] at hx
                    exact ne_of_gt (lt_of_lt_of_le hiH hx.1))
                  (hφi _ _ hiH hT1pos)
                  (fun x hx => hφlb x hx.1)
                rw [intervalIntegral.integral_const_mul, integral_one_div] at hm
                · have : T1 / (1 / (H:ℝ)) = Real.exp (c0 / (1 - c0)) := by
                    rw [hT1]; field_simp
                  rw [this, Real.log_exp] at hm
                  have : (1 - c0) * (c0 / (1 - c0)) = c0 := by
                    have : 1 - c0 ≠ 0 := by linarith
                    field_simp
                  linarith
                · rw [Set.uIcc_of_le hT1ge]
                  intro h
                  exact absurd h.1 (not_le.2 hiH)
              have hcon : ContinuousOn (fun T => ∫ τ in (1/(H:ℝ))..T, fH H (1/τ)) (Set.Icc (1/(H:ℝ)) T1) := by
                rw [← Set.uIcc_of_le hT1ge]
                apply intervalIntegral.continuousOn_primitive_interval
                apply ContinuousOn.integrableOn_compact isCompact_uIcc
                apply hφc.mono
                intro x hx
                rw [Set.uIcc_of_le hT1ge] at hx
                exact lt_of_lt_of_le hiH hx.1
              obtain ⟨T, hTmem, hTeq⟩ := intermediate_value_Icc hT1ge hcon
                ⟨by simp [hc0pos.le], hbig⟩
              refine ⟨T, ?_, (hroot T).2 hTeq⟩
              rcases hTmem.1.lt_or_eq with h | h
              · exact h
              · rw [← h] at hTeq; simp at hTeq; linarith
            refine ⟨?_, ?_⟩
            · obtain ⟨T, hT, hTr⟩ := hexists
              refine ⟨T, ⟨hT, hTr⟩, ?_⟩
              rintro T' ⟨hT', hT'r⟩
              rw [hroot] at hTr hT'r
              rcases lt_trichotomy T' T with h | h | h
              · have := huniq T' T hT' h; linarith
              · exact h
              · have := huniq T T' hT h; linarith
            intro T hT hTr
            rw [hroot] at hTr
            have hTpos : 0 < T := hiH.trans hT
            have hiT : 1 / T < H := by
              rw [div_lt_iff₀ hTpos]; rw [div_lt_iff₀ hHpos] at hT; linarith
            have hHT : 1 < (H:ℝ) * T := by rw [div_lt_iff₀ hHpos] at hT; linarith
            set ss : ℝ → ℝ := fun τ => if τ ≤ 1/(H:ℝ) then (H:ℝ) else if τ ≤ T then 1/τ else 0 with hss
            have hss_meas : Measurable ss := by
              refine Measurable.ite measurableSet_Iic measurable_const
                (Measurable.ite measurableSet_Iic (measurable_const.div measurable_id) measurable_const)
            have hss1 : ∀ τ ∈ Set.Icc (0:ℝ) (1/(H:ℝ)), ss τ = H := by
              intro τ hτ; simp only [hss, if_pos hτ.2]
            have hss2 : ∀ τ ∈ Set.Ioc (1/(H:ℝ)) T, ss τ = 1/τ := by
              intro τ hτ; simp only [hss, if_neg (not_le.2 hτ.1), if_pos hτ.2]
            have hss3 : ∀ τ ∈ Set.Ioi T, ss τ = 0 := by
              intro τ hτ
              have hτ' : T < τ := hτ
              simp only [hss, if_neg (not_le.2 (hT.trans hτ')), if_neg (not_le.2 hτ')]
            have hss_nn : ∀ τ, 0 ≤ ss τ := by
              intro τ; simp only [hss]; split_ifs with h1 h2
              · exact hHpos.le
              · have : 0 < τ := hiH.trans (not_le.1 h1); positivity
              · exact le_rfl
            have hsplit : ∀ g : ℝ → ℝ≥0∞, ∫⁻ τ in Set.Ici 0, g τ = (∫⁻ τ in Set.Icc 0 (1/(H:ℝ)), g τ) +
                (∫⁻ τ in Set.Ioc (1/(H:ℝ)) T, g τ) + ∫⁻ τ in Set.Ioi T, g τ := by
              intro g
              rw [← Set.Icc_union_Ioi_eq_Ici hTpos.le, lintegral_union measurableSet_Ioi
                (Set.disjoint_left.2 (fun x hx hy => by simp at hx hy; linarith)),
                ← Set.Icc_union_Ioc_eq_Icc hiH.le hT.le, lintegral_union measurableSet_Ioc
                (Set.disjoint_left.2 (fun x hx hy => by simp at hx hy; linarith))]
            have hIoc : ∀ φ : ℝ → ℝ, IntervalIntegrable φ volume (1/(H:ℝ)) T →
                (∀ τ ∈ Set.Ioc (1/(H:ℝ)) T, 0 ≤ φ τ) →
                ∫⁻ τ in Set.Ioc (1/(H:ℝ)) T, ENNReal.ofReal (φ τ) = ENNReal.ofReal (∫ τ in (1/(H:ℝ))..T, φ τ) := by
              intro φ hi hnn
              rw [intervalIntegral.integral_of_le hT.le, ofReal_integral_eq_lintegral_ofReal hi.1]
              exact (ae_restrict_mem measurableSet_Ioc).mono (fun x hx => hnn x hx)
            have hlogint : ∫ τ in (1/(H:ℝ))..T, 1/τ = Real.log (H * T) := by
              rw [integral_one_div]
              · congr 1; field_simp
              · rw [Set.uIcc_of_le hT.le]; intro h; exact absurd h.1 (not_le.2 hiH)
            -- the objective of ss
            have hobj : frObj ss = ENNReal.ofReal (1 + Real.log (H * T)) := by
              unfold frObj
              rw [hsplit, setLIntegral_congr_fun measurableSet_Icc (fun τ hτ => by rw [hss1 τ hτ]),
                setLIntegral_congr_fun measurableSet_Ioc (fun τ hτ => by rw [hss2 τ hτ]),
                setLIntegral_congr_fun measurableSet_Ioi (fun τ hτ => by rw [hss3 τ hτ]),
                hIoc (fun τ => 1/τ) ?_ ?_, hlogint]
              · simp only [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_zero, lintegral_zero, add_zero]
                rw [← ENNReal.ofReal_mul hHpos.le, ← ENNReal.ofReal_add (by positivity)
                  (Real.log_nonneg hHT.le)]
                congr 1; rw [sub_zero, mul_one_div_cancel hHpos.ne']
              · apply ContinuousOn.intervalIntegrable
                apply continuousOn_const.div continuousOn_id
                intro x hx; rw [Set.uIcc_of_le hT.le] at hx; exact ne_of_gt (lt_of_lt_of_le hiH hx.1)
              · intro τ hτ; have : 0 < τ := hiH.trans hτ.1; positivity
            -- the constraint of ss is tight
            have hcons : ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (fH H (ss τ)) = 1 := by
              rw [hsplit, setLIntegral_congr_fun measurableSet_Icc (fun τ hτ => by rw [hss1 τ hτ]),
                setLIntegral_congr_fun measurableSet_Ioc (fun τ hτ => by rw [hss2 τ hτ]),
                setLIntegral_congr_fun measurableSet_Ioi (fun τ hτ => by rw [hss3 τ hτ]),
                hIoc (fun τ => fH H (1/τ)) (hφi _ _ hiH hTpos) (fun τ hτ => (hφpos τ (hiH.trans hτ.1)).le),
                hTr, hf0, hfH]
              simp only [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_zero, lintegral_zero, add_zero]
              rw [← ENNReal.ofReal_mul (by nlinarith), ← ENNReal.ofReal_add (by
                apply mul_nonneg (by nlinarith); simp) hc0pos.le]
              rw [← ENNReal.ofReal_one]; congr 1; rw [sub_zero]; field_simp; ring
            have hfeas : FRMultiFeasible H ss := by
              refine ⟨?_, ?_, hcons.le⟩
              · intro a ha b hb hab
                simp only [hss]
                have ha' : (0:ℝ) ≤ a := ha
                split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
                all_goals first
                  | exact le_rfl
                  | exact hHpos.le
                  | (exfalso; linarith)
                  | exact div_nonneg zero_le_one ha'
                  | exact one_div_le_one_div_of_le (hiH.trans (not_le.1 ‹¬a ≤ 1 / (H:ℝ)›)) hab
                  | (have hb0 : 0 < b := hiH.trans (not_le.1 ‹¬b ≤ 1 / (H:ℝ)›)
                     rw [div_le_iff₀ hb0]; have := not_le.1 ‹¬b ≤ 1 / (H:ℝ)›
                     rw [div_lt_iff₀ hHpos] at this; linarith)
              · intro τ hτ
                simp only [hss]
                split_ifs with h1 h2
                · refine ⟨hHpos.le, le_rfl, ?_⟩
                  rw [le_div_iff₀ hHpos] at h1; linarith
                · have : 0 < τ := hiH.trans (not_le.1 h1)
                  refine ⟨by positivity, ?_, ?_⟩
                  · rw [div_le_iff₀ this]; have := not_le.1 h1; rw [div_lt_iff₀ hHpos] at this; linarith
                  · rw [mul_one_div_cancel this.ne']
                · simp
            set a : ℝ := fH H (1/T) with ha
            have hapos : 0 < a := hfpos _ (by positivity)
            set lam : ℝ := 1 / (T * a) with hlam
            have hlampos : 0 < lam := by positivity
            have hlamTa : lam * (T * a) = 1 := by rw [hlam]; field_simp
            have hssle : ∀ τ, τ ≤ T → 1/T ≤ ss τ := by
              intro τ hτ; simp only [hss]; split_ifs with h1
              · exact hiT.le
              · have : 0 < τ := hiH.trans (not_le.1 h1)
                exact one_div_le_one_div_of_le this hτ
            have hxle : ∀ τ, 0 ≤ τ → τ ≤ T → ∀ x : ℝ, x ≤ (H:ℝ) → τ * x ≤ 1 → x ≤ ss τ := by
              intro τ hτ0 hτ x hxH hτx; simp only [hss]; split_ifs with h1
              · exact hxH
              · have : 0 < τ := hiH.trans (not_le.1 h1)
                rw [le_div_iff₀ this]; linarith
            have hfm : ∀ τ, τ ≤ T → fH H (ss τ) ≤ T * a * ss τ := by
              intro τ hτ
              have e2 := hkey (1/T) (ss τ) (by positivity) (hssle τ hτ)
              have := mul_le_mul_of_nonneg_left e2 hTpos.le
              rw [← mul_assoc, mul_one_div_cancel hTpos.ne', one_mul] at this; linarith
            set g : ℝ → ℝ := fun τ => ss τ - lam * fH H (ss τ) with hg
            have hg_nn : ∀ τ, 0 ≤ g τ := by
              intro τ
              rcases le_or_gt τ T with hτ | hτ
              · have := mul_le_mul_of_nonneg_left (hfm τ hτ) hlampos.le
                have h3 : lam * (T * a * ss τ) = ss τ := by
                  rw [show T * a * ss τ = (T * a) * ss τ by ring, ← mul_assoc, hlamTa, one_mul]
                simp only [hg]; linarith
              · simp only [hg, hss3 τ hτ, hf0]; simp
            have hpt : ∀ τ, 0 ≤ τ → ∀ x : ℝ, 0 ≤ x → x ≤ (H:ℝ) → τ * x ≤ 1 → x ≤ g τ + lam * fH H x := by
              intro τ hτ0 x hx0 hxH hτx
              rcases le_or_gt τ T with hτ | hτ
              · have hm1 := hssle τ hτ
                have hm0 : 0 < ss τ := lt_of_lt_of_le (by positivity) hm1
                have hxm := hxle τ hτ0 hτ x hxH hτx
                have e1 := hkey x (ss τ) hx0 hxm
                have e2 := hfm τ hτ
                have e3 : (x - ss τ) * (T * a * ss τ - fH H (ss τ)) ≤ 0 :=
                  mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
                have h4 : (x - ss τ) * (T * a) ≤ fH H x - fH H (ss τ) := by
                  have : ss τ * ((x - ss τ) * (T * a)) ≤ ss τ * (fH H x - fH H (ss τ)) := by nlinarith
                  exact le_of_mul_le_mul_left this hm0
                have h5 := mul_le_mul_of_nonneg_left h4 hlampos.le
                rw [show lam * ((x - ss τ) * (T * a)) = (x - ss τ) * (lam * (T * a)) by ring, hlamTa,
                  mul_one] at h5
                simp only [hg]; nlinarith
              · simp only [hg, hss3 τ hτ, hf0, mul_zero, sub_zero, zero_add]
                have hxT : x ≤ 1/T := by
                  rw [le_div_iff₀ hTpos]; nlinarith
                have e := hkey x (1/T) hx0 hxT
                have : x * (T * a) ≤ fH H x := by
                  have := mul_le_mul_of_nonneg_left e hTpos.le
                  rw [← mul_assoc T (1/T), mul_one_div_cancel hTpos.ne', one_mul] at this; linarith
                have h5 := mul_le_mul_of_nonneg_left this hlampos.le
                rw [show lam * (x * (T * a)) = x * (lam * (T * a)) by ring, hlamTa, mul_one] at h5
                exact h5
            have hg_meas : Measurable (fun τ => ENNReal.ofReal (g τ)) := by
              apply ENNReal.measurable_ofReal.comp
              exact hss_meas.sub (measurable_const.mul (hcont.measurable.comp hss_meas))
            have hdecomp : ∀ τ, ENNReal.ofReal (ss τ) =
                ENNReal.ofReal (g τ) + ENNReal.ofReal lam * ENNReal.ofReal (fH H (ss τ)) := by
              intro τ
              rw [← ENNReal.ofReal_mul hlampos.le, ← ENNReal.ofReal_add (hg_nn τ)
                (mul_nonneg hlampos.le (hfnn _ (hss_nn τ)))]
              congr 1; simp only [hg]; ring
            have hub : ∀ s, FRMultiFeasible H s → frObj s ≤ ENNReal.ofReal (1 + Real.log (H * T)) := by
              rintro s ⟨_, hb, hc⟩
              rw [← hobj]
              unfold frObj
              calc ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (s τ)
                  ≤ ∫⁻ τ in Set.Ici 0, (ENNReal.ofReal (g τ) +
                      ENNReal.ofReal lam * ENNReal.ofReal (fH H (s τ))) := by
                    apply setLIntegral_mono' measurableSet_Ici
                    intro τ hτ
                    obtain ⟨h0, h1, h2⟩ := hb τ hτ
                    rw [← ENNReal.ofReal_mul hlampos.le, ← ENNReal.ofReal_add (hg_nn τ)
                      (mul_nonneg hlampos.le (hfnn _ h0))]
                    exact ENNReal.ofReal_le_ofReal (hpt τ hτ (s τ) h0 h1 h2)
                _ = (∫⁻ τ in Set.Ici 0, ENNReal.ofReal (g τ)) +
                      ENNReal.ofReal lam * ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (fH H (s τ)) := by
                    rw [lintegral_add_left hg_meas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                _ ≤ (∫⁻ τ in Set.Ici 0, ENNReal.ofReal (g τ)) +
                      ENNReal.ofReal lam * ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (fH H (ss τ)) := by
                    rw [hcons]; gcongr
                _ = ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (ss τ) := by
                    rw [show (fun τ => ENNReal.ofReal (ss τ)) = fun τ => ENNReal.ofReal (g τ) +
                      ENNReal.ofReal lam * ENNReal.ofReal (fH H (ss τ)) from funext hdecomp,
                      lintegral_add_left hg_meas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            have hgreat : IsGreatest (frMultiValues H) (ENNReal.ofReal (1 + Real.log (H * T))) :=
              ⟨⟨ss, hfeas, hobj⟩, by rintro _ ⟨s, hs, rfl⟩; exact hub s hs⟩
            have hsup : sSup (frMultiValues H) = ENNReal.ofReal (1 + Real.log (H * T)) := hgreat.csSup_eq
            have hlogpos := Real.log_pos hHT
            refine ⟨⟨?_, ?_, ?_⟩, hsup⟩
            · rw [hsup]; exact hgreat
            · rw [hsup]; exact ENNReal.ofReal_pos.2 (by linarith)
            · rw [hsup]; exact ENNReal.ofReal_ne_top
