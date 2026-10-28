-- Prove2me | solution 1 for RobustSPA.IID.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:27:03.127848+00:00
-- url     : https://prove2.me/submissions/c43d6a30-50c6-4aef-86c0-4456fa09bce3

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting
import Definitions.Def_RobustSPA_Affiliated_Setting
import Theorems.Thm_RobustSPA_IID_proposition_A_3
import Theorems.Thm_RobustSPA_IID_step_1_nature
import Theorems.Thm_RobustSPA_IID_step_2_seller
import Theorems.Thm_RobustSPA_IID_SPA_isDSIC
import Theorems.Thm_RobustSPA_Affiliated_Fiid_subset_Faff

open MeasureTheory Set Filter Topology RobustSPA.IID

namespace RSPAThm1

/-- A monotone right-continuous function which is `0` up to `a` and `1` from `b` on is the CDF
of a probability measure. -/
lemma exists_prob_of_cdf (f : ℝ → ℝ) (hm : Monotone f) (hrc : ∀ x, ContinuousWithinAt f (Ici x) x)
    (a b : ℝ) (h0 : ∀ x ≤ a, f x = 0) (h1 : ∀ x, b ≤ x → f x = 1) :
    ∃ ρ : ProbabilityMeasure ℝ, ∀ t, cdfOf ρ t = f t := by
  let F : StieltjesFunction ℝ := ⟨f, hm, hrc⟩
  have hF : ∀ x, F x = f x := fun x => rfl
  have hbot : Tendsto F atBot (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_atBot.2 ⟨a, fun x hx => by rw [hF, h0 x hx]⟩)
  have htop : Tendsto F atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨b, fun x hx => by rw [hF, h1 x hx]⟩)
  have := F.isProbabilityMeasure hbot htop
  refine ⟨⟨F.measure, this⟩, fun t => ?_⟩
  show (F.measure (Iic t)).toReal = f t
  have hnn : 0 ≤ f t := by
    rw [← h0 (min t a) (min_le_right _ _)]; exact hm (min_le_left _ _)
  rw [F.measure_Iic hbot t, sub_zero, ENNReal.toReal_ofReal (by rw [hF]; exact hnn), hF]

/-- A law whose CDF vanishes at `a` and equals `1` at `b` lives on `[a, b]`. -/
lemma supp_of_cdf (G : ProbabilityMeasure ℝ) (a b : ℝ) (ha : cdfOf G a = 0) (hb : cdfOf G b = 1) :
    (G : Measure ℝ) (Set.Icc a b)ᶜ = 0 := by
  have h0 : (G : Measure ℝ) (Set.Iic a) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp ha with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have h1 : (G : Measure ℝ) (Set.Iic b) = 1 := by
    have hne : (G : Measure ℝ) (Set.Iic b) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hne]
    simp only [cdfOf] at hb
    rw [hb, ENNReal.ofReal_one]
  have h2 : (G : Measure ℝ) (Set.Ioi b) = 0 := by
    rw [← Set.compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic]
    exact h1
  have hsub : (Set.Icc a b)ᶜ ⊆ Set.Iic a ∪ Set.Ioi b := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl (le_of_lt hx)
    · exact Or.inr hx
  apply le_antisymm _ bot_le
  calc (G : Measure ℝ) (Set.Icc a b)ᶜ ≤ (G : Measure ℝ) (Set.Iic a ∪ Set.Ioi b) := measure_mono hsub
    _ ≤ (G : Measure ℝ) (Set.Iic a) + (G : Measure ℝ) (Set.Ioi b) := measure_union_le _ _
    _ = 0 := by rw [h0, h2, add_zero]

/-- Regret of a DSIC mechanism is bounded above uniformly over laws supported on the cube. -/
lemma regret_bdd {n : ℕ} (hn : 0 < n) (m : Mechanism n) (hm : m.IsDSIC) :
    ∃ C : ℝ, ∀ μ ∈ Fall n, regret m μ ≤ C := by
  obtain ⟨B, hB⟩ := hm.p_bdd
  refine ⟨1 + n * |B|, fun μ hμ => ?_⟩
  haveI := hμ.1
  have hae : ∀ᵐ v ∂μ, v ∈ cube n := by
    rw [ae_iff]
    simpa [Set.compl_def] using hμ.2
  have hC : 0 ≤ 1 + n * |B| := by positivity
  by_cases hint : Integrable (fun v => top v - ∑ i, m.p i v) μ
  · unfold regret
    calc ∫ v, (top v - ∑ i, m.p i v) ∂μ ≤ ∫ _v, (1 + n * |B|) ∂μ := by
          apply integral_mono_ae hint (integrable_const _)
          filter_upwards [hae] with v hv
          have htop : top v ≤ 1 := by
            haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
            exact ciSup_le fun i => (hv i (Set.mem_univ _)).2
          have hs : -(∑ i, m.p i v) ≤ n * |B| := by
            rw [← Finset.sum_neg_distrib]
            calc ∑ i, -m.p i v ≤ ∑ _i : Fin n, |B| := Finset.sum_le_sum fun i _ => by
                  have h1 := hB v hv i
                  have h2 := le_abs_self B
                  have h3 := neg_le_abs (m.p i v)
                  linarith
              _ = n * |B| := by simp
          linarith
      _ = 1 + n * |B| := by simp
  · unfold regret
    rw [integral_undef hint]
    exact hC

end RSPAThm1

open RSPAThm1 in
theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 ∧
      (∀ r' ∈ Set.Ioo (0 : ℝ) 1, rEq n r' = 0 → r' = r) ∧
      ∃ ρ : ProbabilityMeasure ℝ,
        (ρ : Measure ℝ) (Set.Icc r 1)ᶜ = 0 ∧
        (∀ t, cdfOf ρ t = PhiStar n r t) ∧
        (SPA (n := n) (ρ : Measure ℝ)).IsDSIC ∧
        (∀ μ ∈ Fiid n, regret (SPA (ρ : Measure ℝ)) μ ≤ value n r) ∧
        (∀ m : Mechanism n, m.IsDSIC → ∃ μ ∈ Fiid n, value n r ≤ regret m μ) ∧
        minimaxRegret n (Fiid n) = value n r := by
  obtain ⟨⟨r, hr, hrEq, huniq⟩, hrest⟩ := proposition_A_3 n hn
  obtain ⟨hser, hD, hlim, hΦ1, hval⟩ := hrest r hr hrEq
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  -- the reserve law
  have hΦnn : ∀ v ∈ Ioc r 1, 0 ≤ PhiStar n r v := fun v hv =>
    (hser v hv).nonneg fun j => by
      have hv0 : 0 < v := lt_trans hr0 hv.1
      have : 0 ≤ (v - r) / v := div_nonneg (by linarith [hv.1]) hv0.le
      positivity
  have hΦmono_on : ∀ v ∈ Ioc r 1, ∀ w ∈ Ioc r 1, v ≤ w → PhiStar n r v ≤ PhiStar n r w := by
    intro v hv w hw hvw
    refine hasSum_le (fun j => ?_) (hser v hv) (hser w hw)
    have hv0 : 0 < v := lt_trans hr0 hv.1
    have hw0 : 0 < w := lt_trans hr0 hw.1
    have e1 : 0 ≤ (v - r) / v := div_nonneg (by linarith [hv.1]) hv0.le
    have e2 : (v - r) / v ≤ (w - r) / w := by
      rw [div_le_div_iff₀ hv0 hw0]; nlinarith
    have : 0 ≤ 1 / ((j + n : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ e1 e2 _) this
  have hΦle1 : ∀ v ∈ Ioc r 1, PhiStar n r v ≤ 1 := fun v hv =>
    hΦ1 ▸ hΦmono_on v hv 1 ⟨hr1, le_rfl⟩ hv.2
  have hΦlo : ∀ v ≤ r, PhiStar n r v = 0 := fun v hv => by unfold PhiStar; rw [if_pos hv]
  have hΦhi : ∀ v, 1 < v → PhiStar n r v = 1 := fun v hv => by
    unfold PhiStar; rw [if_neg (by linarith), if_neg (by linarith)]
  have hΦmono : Monotone (PhiStar n r) := by
    intro v w hvw
    rcases le_or_gt v r with h1 | h1
    · rw [hΦlo v h1]
      rcases le_or_gt w r with h2 | h2
      · rw [hΦlo w h2]
      rcases le_or_gt w 1 with h3 | h3
      · exact hΦnn w ⟨h2, h3⟩
      · rw [hΦhi w h3]; norm_num
    rcases le_or_gt v 1 with h3 | h3
    · rcases le_or_gt w 1 with h4 | h4
      · exact hΦmono_on v ⟨h1, h3⟩ w ⟨lt_of_lt_of_le h1 hvw, h4⟩ hvw
      · rw [hΦhi w h4]; exact hΦle1 v ⟨h1, h3⟩
    · rw [hΦhi v h3, hΦhi w (lt_of_lt_of_le h3 hvw)]
  have hΦrc : ∀ x, ContinuousWithinAt (PhiStar n r) (Ici x) x := by
    intro x
    rcases lt_trichotomy x r with h | h | h
    · apply ContinuousAt.continuousWithinAt
      have : PhiStar n r =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        (eventually_lt_nhds h).mono fun y hy => hΦlo y hy.le
      exact (continuousAt_const).congr this.symm
    · subst h
      have : ContinuousWithinAt (PhiStar n x) (Ioi x) x := by
        rw [ContinuousWithinAt, hΦlo x le_rfl]; exact hlim
      exact continuousWithinAt_Ioi_iff_Ici.mp this
    rcases lt_or_ge x 1 with h' | h'
    · exact (hD x ⟨h, h'⟩).continuousAt.continuousWithinAt
    · have hc : ∀ y ∈ Ici x, PhiStar n r y = 1 := by
        intro y hy
        rcases eq_or_lt_of_le (le_trans h' hy) with e | e
        · rw [← e, hΦ1]
        · exact hΦhi y e
      exact continuousWithinAt_const.congr hc (hc x (mem_Ici.mpr le_rfl))
  obtain ⟨ρ, hρ⟩ := exists_prob_of_cdf (PhiStar n r) hΦmono hΦrc r 2 hΦlo
    (fun x hx => hΦhi x (by linarith))
  -- the isorevenue law
  have hisoMono : Monotone (isoCDF r) := by
    intro s t hst
    have k1 : ∀ u, r ≤ u → 0 ≤ r / u ∧ r / u ≤ 1 := fun u hu => by
      have hu0 : 0 < u := lt_of_lt_of_le hr0 hu
      exact ⟨div_nonneg hr0.le hu0.le, (div_le_one hu0).mpr hu⟩
    have k2 : r ≤ s → r / t ≤ r / s := fun hs =>
      div_le_div_of_nonneg_left hr0.le (lt_of_lt_of_le hr0 hs) hst
    unfold isoCDF
    split_ifs <;> first
      | (norm_num; done)
      | (have := k1 t (by linarith); linarith)
      | (have := k1 s (by linarith); linarith)
      | (have := k2 (by linarith); linarith)
  have hisoRc : ∀ x, ContinuousWithinAt (isoCDF r) (Ici x) x := by
    intro x
    rcases lt_or_ge x r with h | h
    · apply ContinuousAt.continuousWithinAt
      have : isoCDF r =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        (eventually_lt_nhds h).mono fun y hy => by unfold isoCDF; rw [if_pos hy]
      exact (continuousAt_const).congr this.symm
    rcases lt_or_ge x 1 with h' | h'
    · have hx0 : 0 < x := lt_of_lt_of_le hr0 h
      have hc : ContinuousWithinAt (fun t => 1 - r / t) (Ici x) x :=
        (continuousAt_const.sub (continuousAt_const.div continuousAt_id hx0.ne')).continuousWithinAt
      have hcx : ContinuousWithinAt (isoCDF r) (Ico x 1) x := by
        apply hc.mono Ico_subset_Ici_self |>.congr
        · intro y hy
          unfold isoCDF
          rw [if_neg (by linarith [hy.1]), if_pos hy.2]
        · unfold isoCDF; rw [if_neg (by linarith), if_pos h']
      apply hcx.mono_of_mem_nhdsWithin
      apply Filter.mem_of_superset (inter_mem_nhdsWithin (Ici x) (Iio_mem_nhds h'))
      intro y hy; exact ⟨hy.1, hy.2⟩
    · have hc : ∀ y ∈ Ici x, isoCDF r y = 1 := by
        intro y hy
        have hy' : (1 : ℝ) ≤ y := le_trans h' hy
        unfold isoCDF; rw [if_neg (by linarith), if_neg (by linarith)]
      exact continuousWithinAt_const.congr hc (hc x (mem_Ici.mpr le_rfl))
  obtain ⟨G, hG⟩ := exists_prob_of_cdf (isoCDF r) hisoMono hisoRc 0
    1 (fun x hx => by unfold isoCDF; rw [if_pos (by linarith)])
    (fun x hx => by unfold isoCDF; rw [if_neg (by linarith), if_neg (by linarith)])
  have hGsupp : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 := by
    apply supp_of_cdf G 0 1
    · rw [hG]; unfold isoCDF; rw [if_pos hr0]
    · rw [hG]; unfold isoCDF; rw [if_neg (by linarith), if_neg (by linarith)]
  have hρsupp : (ρ : Measure ℝ) (Set.Icc r 1)ᶜ = 0 := by
    apply supp_of_cdf ρ r 1
    · rw [hρ]; exact hΦlo r le_rfl
    · rw [hρ]; exact hΦ1
  set Gn : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => (G : Measure ℝ) with hGn_def
  set S : Mechanism n := SPA (ρ : Measure ℝ) with hS_def
  have hS : S.IsDSIC := SPA_isDSIC n ρ
  have hGn_iid : Gn ∈ Fiid n := ⟨G, hGsupp, rfl⟩
  have hv : regret S Gn = value n r := hval ρ G hρ hG
  have part1 : ∀ μ ∈ Fiid n, regret S μ ≤ value n r := fun μ hμ =>
    (step_1_nature n hn r hr hrEq ρ G hρ hG μ hμ).trans hv.le
  have part2 : ∀ m : Mechanism n, m.IsDSIC → value n r ≤ regret m Gn := fun m hm =>
    hv.symm.le.trans (step_2_seller n hn r hr hrEq ρ G hρ hG m hm)
  refine ⟨r, hr, hrEq, huniq, ρ, hρsupp, hρ, hS, part1, fun m hm => ⟨Gn, hGn_iid, part2 m hm⟩, ?_⟩
  -- the minimax value
  have hFall : ∀ μ ∈ Fiid n, μ ∈ Fall n := fun μ hμ =>
    (RobustSPA.Affiliated.Fiid_subset_Faff n hμ).1.1
  unfold minimaxRegret
  have hbdd : ∀ m : {m : Mechanism n // m.IsDSIC},
      BddAbove (Set.range fun μ : Fiid n => regret m.1 (μ : Measure (Fin n → ℝ))) := by
    intro m
    obtain ⟨C, hC⟩ := regret_bdd hn m.1 m.2
    exact ⟨C, by rintro _ ⟨μ, rfl⟩; exact hC μ (hFall μ μ.2)⟩
  have hsup_ge : ∀ m : {m : Mechanism n // m.IsDSIC},
      value n r ≤ ⨆ μ : Fiid n, regret m.1 (μ : Measure (Fin n → ℝ)) := fun m =>
    (part2 m.1 m.2).trans (le_ciSup (f := fun μ : Fiid n => regret m.1 (μ : Measure (Fin n → ℝ)))
      (hbdd m) ⟨Gn, hGn_iid⟩)
  apply le_antisymm
  · refine (ciInf_le ⟨value n r, ?_⟩ ⟨S, hS⟩).trans ?_
    · rintro _ ⟨m, rfl⟩; exact hsup_ge m
    · haveI : Nonempty (Fiid n) := ⟨⟨Gn, hGn_iid⟩⟩
      exact ciSup_le fun μ => part1 μ μ.2
  · haveI : Nonempty {m : Mechanism n // m.IsDSIC} := ⟨⟨S, hS⟩⟩
    exact le_ciInf hsup_ge
