-- Prove2me | solution 1 for RankBasedSDI.LoadBalancing.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:00:46.37141+00:00
-- url     : https://prove2.me/submissions/bcae1dbf-4fef-4aba-b335-1d11be6e96d4

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

namespace RBLem42Aux

noncomputable def gam (x : ℝ → ℝ) (t : ℝ) : ℝ := x t + skorokhodReg x t

lemma cadlag_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (t : ℝ) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc 0 t, |x s| ≤ M := by
  have hc : IsCompact (Set.Icc (0:ℝ) t) := isCompact_Icc
  refine hc.induction_on (p := fun S => ∃ M : ℝ, ∀ s ∈ S, |x s| ≤ M) ⟨0, by simp⟩ ?_ ?_ ?_
  · intro S T hST ⟨M, hM⟩
    exact ⟨M, fun s hs => hM s (hST hs)⟩
  · intro S T ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨max M N, fun s hs => ?_⟩
    rcases hs with hs | hs
    · exact (hM s hs).trans (le_max_left _ _)
    · exact (hN s hs).trans (le_max_right _ _)
  · intro s hs
    have hr : ∀ᶠ y in 𝓝[≥] s, |x y - x s| < 1 := by
      have := hx.1 s hs.1
      have h2 := this.tendsto.eventually (Metric.ball_mem_nhds (x s) one_pos)
      filter_upwards [h2] with y hy
      simpa [Real.dist_eq] using hy
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0
      refine ⟨{y | |x y - x 0| < 1}, ?_, |x 0| + 1, ?_⟩
      · exact nhdsWithin_mono _ (fun y hy => hy.1) hr
      · intro y hy
        have := abs_sub_abs_le_abs_sub (x y) (x 0)
        simp only [Set.mem_setOf_eq] at hy
        linarith
    · obtain ⟨l, hl⟩ := hx.2 s hpos
      have hlft : ∀ᶠ y in 𝓝[<] s, |x y - l| < 1 := by
        have h2 := hl.eventually (Metric.ball_mem_nhds l one_pos)
        filter_upwards [h2] with y hy
        simpa [Real.dist_eq] using hy
      refine ⟨{y | |x y - x s| < 1} ∪ {y | |x y - l| < 1}, ?_, max (|x s|) (|l|) + 1, ?_⟩
      · apply mem_nhdsWithin_of_mem_nhds
        rw [← nhdsLT_sup_nhdsGE]
        exact ⟨Filter.mem_of_superset hlft (fun y hy => Or.inr hy),
          Filter.mem_of_superset hr (fun y hy => Or.inl hy)⟩
      · intro y hy
        rcases hy with hy | hy
        · have := abs_sub_abs_le_abs_sub (x y) (x s)
          simp only [Set.mem_setOf_eq] at hy
          have := le_max_left (|x s|) (|l|)
          linarith
        · have := abs_sub_abs_le_abs_sub (x y) l
          simp only [Set.mem_setOf_eq] at hy
          have := le_max_right (|x s|) (|l|)
          linarith

variable (x : ℝ → ℝ) (hx : IsCadlag x)
include hx

lemma reg_bdd (t : ℝ) : BddAbove ((fun s => max (-x s) 0) '' Set.Icc 0 t) := by
  obtain ⟨M, hM⟩ := cadlag_bdd x hx t
  refine ⟨max M 0, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have := hM s hs
  have := neg_abs_le (x s)
  exact max_le_max (by linarith) le_rfl

lemma le_reg {t r : ℝ} (hr : r ∈ Set.Icc 0 t) : max (-x r) 0 ≤ skorokhodReg x t :=
  le_csSup (reg_bdd x hx t) (Set.mem_image_of_mem _ hr)

omit hx in
lemma reg_le {t c : ℝ} (ht : 0 ≤ t) (h : ∀ r ∈ Set.Icc 0 t, max (-x r) 0 ≤ c) :
    skorokhodReg x t ≤ c := by
  apply csSup_le ((Set.nonempty_Icc.2 ht).image _)
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

lemma reg_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ skorokhodReg x t :=
  (le_max_right _ _).trans (le_reg x hx ⟨le_rfl, ht⟩)

lemma neg_le_reg {t r : ℝ} (hr : r ∈ Set.Icc 0 t) : -x r ≤ skorokhodReg x t :=
  (le_max_left _ _).trans (le_reg x hx hr)

lemma reg_zero (hx0 : 0 ≤ x 0) : skorokhodReg x 0 = 0 := by
  apply le_antisymm
  · apply reg_le x le_rfl
    intro r hr
    have : r = 0 := le_antisymm hr.2 hr.1
    subst this
    simp [hx0]
  · exact reg_nonneg x hx le_rfl

lemma reg_mono : MonotoneOn (skorokhodReg x) (Set.Ici 0) := by
  intro a ha b hb hab
  apply reg_le x (show (0:ℝ) ≤ a from ha)
  intro r hr
  exact le_reg x hx ⟨hr.1, hr.2.trans hab⟩


/-- If `-x ≤ R t + c` on `[t, s]` then `R s ≤ R t + c`. -/
lemma reg_le_of_near {t s c : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hc : 0 ≤ c)
    (h : ∀ r ∈ Set.Icc t s, -x r ≤ skorokhodReg x t + c) :
    skorokhodReg x s ≤ skorokhodReg x t + c := by
  apply reg_le x (ht.trans hts)
  intro r hr
  rcases le_or_gt r t with hrt | hrt
  · exact (le_reg x hx ⟨hr.1, hrt⟩).trans (by linarith)
  · have h1 := h r ⟨hrt.le, hr.2⟩
    have h2 := reg_nonneg x hx ht
    exact max_le h1 (by linarith)

lemma eventually_near {t η : ℝ} (ht : 0 ≤ t) (hη : 0 < η) :
    ∃ δ > 0, ∀ r ∈ Set.Ico t (t + δ), |x r - x t| < η := by
  have hc := hx.1 t ht
  have h2 : ∀ᶠ y in 𝓝[≥] t, |x y - x t| < η := by
    have := hc.tendsto.eventually (Metric.ball_mem_nhds (x t) hη)
    filter_upwards [this] with y hy
    simpa [Real.dist_eq] using hy
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h2
  refine ⟨u - t, by simpa using hu, fun r hr => hsub ?_⟩
  simpa using hr

lemma reg_rightcont {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (skorokhodReg x) (Set.Ici t) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := eventually_near x hx ht (half_pos hε)
  refine ⟨δ, hδ, fun {s} hs hd => ?_⟩
  have hts : t ≤ s := hs
  rw [Real.dist_eq, abs_lt] at hd
  have hup := reg_le_of_near x hx ht hts (half_pos hε).le (fun r hr => by
    have h1 := hnear r ⟨hr.1, by linarith [hr.2]⟩
    have h2 := neg_le_reg x hx (t := t) (r := t) ⟨ht, le_rfl⟩
    have := (abs_lt.1 h1).1
    linarith)
  have hlo := reg_mono x hx (show (0:ℝ) ≤ t from ht) (show (0:ℝ) ≤ s from ht.trans hts) hts
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

lemma reg_leftlim {t : ℝ} (ht : 0 < t) : ∃ l : ℝ, Tendsto (skorokhodReg x) (𝓝[<] t) (𝓝 l) := by
  set Rm : ℝ → ℝ := fun s => skorokhodReg x (max s 0)
  have hm : Monotone Rm := by
    intro a b hab
    exact reg_mono x hx (show (0:ℝ) ≤ max a 0 from le_max_right _ _)
      (show (0:ℝ) ≤ max b 0 from le_max_right _ _) (max_le_max hab le_rfl)
  refine ⟨_, (hm.tendsto_nhdsLT t).congr' ?_⟩
  have : Set.Ioo 0 t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht
  filter_upwards [this] with s hs
  simp [Rm, max_eq_left hs.1.le]

lemma reg_cadlag : IsCadlag (skorokhodReg x) :=
  ⟨fun t ht => reg_rightcont x hx ht, fun t ht => reg_leftlim x hx ht⟩

lemma gamma1_cadlag : IsCadlag (gam x) := by
  refine ⟨fun t ht => (hx.1 t ht).add (reg_rightcont x hx ht), fun t ht => ?_⟩
  obtain ⟨l1, h1⟩ := hx.2 t ht
  obtain ⟨l2, h2⟩ := reg_leftlim x hx ht
  exact ⟨l1 + l2, h1.add h2⟩

lemma gamma1_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gam x t := by
  have := neg_le_reg x hx (t := t) (r := t) ⟨ht, le_rfl⟩
  simp only [gam]
  linarith


/-- The extension by `0` to negative times of a function that is nonneg, monotone and
right-continuous on `[0, ∞)` and vanishes at `0` is a Stieltjes function. -/
noncomputable def extStieltjes (y : ℝ → ℝ) (hpos : ∀ t, 0 ≤ t → 0 ≤ y t)
    (hmono : MonotoneOn y (Set.Ici 0))
    (hrc : ∀ t, 0 ≤ t → ContinuousWithinAt y (Set.Ici t) t) : StieltjesFunction ℝ where
  toFun := fun t => if 0 ≤ t then y t else 0
  mono' := by
    intro a b hab
    by_cases ha : 0 ≤ a
    · simp only [ha, (ha.trans hab), if_true]
      exact hmono ha (ha.trans hab) hab
    · simp only [ha, if_false]
      split_ifs with hb
      · exact hpos b hb
      · exact le_rfl
  right_continuous' := by
    intro t
    by_cases ht : 0 ≤ t
    · apply (hrc t ht).congr
      · intro s hs
        have : 0 ≤ s := ht.trans hs
        simp [this]
      · simp [ht]
    · push Not at ht
      apply ContinuousWithinAt.mono _ (Set.subset_univ _)
      rw [continuousWithinAt_univ]
      have : (fun t : ℝ => if 0 ≤ t then y t else 0) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        simp [not_le.2 (show s < 0 from hs)]
      exact (continuousAt_const.congr this.symm)


section compl

noncomputable def regG : StieltjesFunction ℝ :=
  extStieltjes (skorokhodReg x) (fun _ ht => reg_nonneg x hx ht)
    (reg_mono x hx) (fun _ ht => reg_rightcont x hx ht)

lemma regG_apply (t : ℝ) : regG x hx t = if 0 ≤ t then skorokhodReg x t else 0 := rfl

lemma regG_nonneg (t : ℝ) : 0 ≤ regG x hx t := by
  rw [regG_apply]; split_ifs with h
  · exact reg_nonneg x hx h
  · exact le_rfl

lemma regG_noJump {t : ℝ} (ht : 0 ≤ t) (hpos : 0 < gam x t) :
    Function.leftLim (regG x hx) t = regG x hx t := by
  have hm : Monotone (regG x hx) := (regG x hx).mono
  apply le_antisymm (hm.leftLim_le le_rfl)
  have hℓ0 : 0 ≤ Function.leftLim (regG x hx) t :=
    (regG_nonneg x hx (t - 1)).trans (hm.le_leftLim (by linarith))
  rw [regG_apply, if_pos ht]
  set ℓ := Function.leftLim (regG x hx) t
  have hbefore : ∀ r ∈ Set.Icc 0 t, r < t → max (-x r) 0 ≤ ℓ := by
    intro r hr hrt
    have h1 := le_reg x hx (t := r) (r := r) ⟨hr.1, le_rfl⟩
    have h2 := hm.le_leftLim hrt
    rw [regG_apply, if_pos hr.1] at h2
    exact h1.trans h2
  have hxt : -x t ≤ ℓ := by
    by_contra hcon
    push Not at hcon
    have : skorokhodReg x t ≤ -x t := by
      apply reg_le x ht
      intro r hr
      rcases lt_or_eq_of_le hr.2 with hrt | hrt
      · exact (hbefore r hr hrt).trans hcon.le
      · subst hrt; exact max_le le_rfl (by linarith)
    simp only [gam] at hpos
    linarith
  apply reg_le x ht
  intro r hr
  rcases lt_or_eq_of_le hr.2 with hrt | hrt
  · exact hbefore r hr hrt
  · subst hrt; exact max_le hxt hℓ0

lemma reg_flat {t : ℝ} (ht : 0 ≤ t) (hpos : 0 < gam x t) :
    ∃ q : ℚ, t < q ∧ skorokhodReg x q = skorokhodReg x t := by
  obtain ⟨δ, hδ, hnear⟩ := eventually_near x hx ht hpos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
  refine ⟨q, hq1, le_antisymm ?_ (reg_mono x hx ht (ht.trans hq1.le) hq1.le)⟩
  have := reg_le_of_near x hx (c := 0) ht hq1.le le_rfl (fun r hr => by
    have h1 := (abs_lt.1 (hnear r ⟨hr.1, lt_of_le_of_lt hr.2 hq2⟩)).1
    simp only [gam] at h1
    linarith)
  simpa using this

lemma regG_null :
    (regG x hx).measure {t | 0 ≤ t ∧ 0 < gam x t} = 0 := by
  set G := regG x hx
  set U := {t | 0 ≤ t ∧ 0 < gam x t}
  set N : Set ℝ := ⋃ (p : ℚ) (q : ℚ) (_ : G p = G q), Set.Ioc (p : ℝ) q
  have hN : G.measure N = 0 := by
    refine measure_iUnion_null fun p => measure_iUnion_null fun q => measure_iUnion_null fun h => ?_
    rw [StieltjesFunction.measure_Ioc, h, sub_self, ENNReal.ofReal_zero]
  have hflat : ∀ t ∈ U, ∃ q : ℚ, t < q ∧ skorokhodReg x q = skorokhodReg x t :=
    fun t ht => reg_flat x hx ht.1 ht.2
  choose! f hf using hflat
  have hinj : Set.InjOn f (U \ N) := by
    have key : ∀ t ∈ U \ N, ∀ t' ∈ U \ N, t < t' → f t ≠ f t' := by
      intro t ht t' ht' htt' hfe
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn htt'
      have hft := hf t ht.1
      have hft' := hf t' ht'.1
      have ht0 : 0 ≤ t := ht.1.1
      have hq0 : (0:ℝ) ≤ (f t' : ℝ) := ht0.trans (htt'.trans hft'.1).le
      have hp0 : (0:ℝ) ≤ (p : ℝ) := ht0.trans hp1.le
      have hRp1 : skorokhodReg x t ≤ skorokhodReg x p := reg_mono x hx ht0 hp0 hp1.le
      have hRp2 : skorokhodReg x p ≤ skorokhodReg x (f t') :=
        reg_mono x hx hp0 hq0 (hp2.trans hft'.1).le
      have hRq : skorokhodReg x (f t') = skorokhodReg x t := by rw [← hfe]; exact hft.2
      have hGeq : G p = G (f t') := by
        simp only [G, regG_apply, if_pos hp0, if_pos hq0]
        linarith
      apply ht'.2
      simp only [N, Set.mem_iUnion]
      exact ⟨p, f t', hGeq, hp2, hft'.1.le⟩
    intro t ht t' ht' hfe
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key t ht t' ht' h hfe
    · exact key t' ht' t ht h hfe.symm
  have hcount : (U \ N).Countable :=
    Set.MapsTo.countable_of_injOn (Set.mapsTo_univ _ _) hinj Set.countable_univ
  have hE : G.measure (U \ N) = 0 := by
    have : U \ N = ⋃ t ∈ U \ N, ({t} : Set ℝ) := (Set.biUnion_of_singleton _).symm
    rw [this, measure_biUnion_null_iff hcount]
    intro t ht
    rw [StieltjesFunction.measure_singleton, regG_noJump x hx ht.1.1 ht.1.2, sub_self,
      ENNReal.ofReal_zero]
  apply measure_mono_null (show U ⊆ (U \ N) ∪ N by intro t ht; by_cases h : t ∈ N <;> simp [h, ht])
  exact measure_union_null hE hN

lemma reg_compl : StieltjesComplementary (gam x) (skorokhodReg x) := by
  refine ⟨regG x hx, regG_apply x hx, ?_⟩
  have : ∀ᵐ t ∂((regG x hx).measure.restrict (Set.Ici 0)),
      ENNReal.ofReal (gam x t) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ici]
    apply measure_mono_null _ (regG_null x hx)
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Ici, ENNReal.ofReal_eq_zero,
      _root_.not_imp, not_le] at ht
    exact ht
  rw [lintegral_congr_ae this, lintegral_zero]

end compl


omit hx in
/-- A positive lower bound for the integrand on a set of positive measure contradicts
complementarity. -/
lemma compl_contra (z : ℝ → ℝ) (G : StieltjesFunction ℝ)
    (hint : ∫⁻ t in Set.Ici 0, ENNReal.ofReal (z t) ∂G.measure = 0)
    (I : Set ℝ) (hI : MeasurableSet I) (hI0 : I ⊆ Set.Ici 0) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ s ∈ I, ε ≤ z s) (hμ : G.measure I ≠ 0) : False := by
  have h1 : ∫⁻ t in I, ENNReal.ofReal ε ∂G.measure ≤ ∫⁻ t in I, ENNReal.ofReal (z t) ∂G.measure :=
    setLIntegral_mono' hI (fun s hs => ENNReal.ofReal_le_ofReal (hz s hs))
  have h2 := lintegral_mono_set (μ := G.measure) (f := fun t => ENNReal.ofReal (z t)) hI0
  rw [setLIntegral_const] at h1
  have : ENNReal.ofReal ε * G.measure I = 0 := le_antisymm (by
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = 0 := hint) bot_le
  rcases mul_eq_zero.1 this with h | h
  · exact (ENNReal.ofReal_pos.2 hε).ne' h
  · exact hμ h


lemma skorokhod_unique' (w v : ℝ → ℝ) (hwpos : ∀ t, 0 ≤ t → 0 ≤ w t)
    (hvpos : ∀ t, 0 ≤ t → 0 ≤ v t) (hwv : ∀ t, 0 ≤ t → w t = x t + v t)
    (hvmono : MonotoneOn v (Set.Ici 0)) (hcompl : StieltjesComplementary w v)
    {t : ℝ} (ht : 0 ≤ t) : v t = skorokhodReg x t := by
  obtain ⟨G, hG, hint⟩ := hcompl
  have hlow : skorokhodReg x t ≤ v t := by
    apply reg_le x ht
    intro r hr
    have := hwv r hr.1
    have := hvmono hr.1 (hr.1.trans hr.2) hr.2
    have := hwpos r hr.1
    exact max_le (by linarith) (hvpos t ht)
  refine le_antisymm ?_ hlow
  by_contra hcon
  push Not at hcon
  set c := skorokhodReg x t
  have hc0 : 0 ≤ c := reg_nonneg x hx ht
  set d := v t - c
  have hd : 0 < d := by simp only [d]; linarith
  have hzlow : ∀ s ∈ Set.Icc 0 t, v s - c ≤ w s := by
    intro s hs
    have := hwv s hs.1
    have := neg_le_reg x hx hs
    linarith
  have hGa : ∀ s, 0 ≤ s → G s = v s := fun s hs => by rw [hG, if_pos hs]
  set S := {s | s ∈ Set.Icc 0 t ∧ v s ≤ c + d / 2}
  by_cases hSne : S.Nonempty
  · obtain ⟨s0, hs0⟩ := hSne
    have hSb : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
    set a := sSup S
    have ha0 : 0 ≤ a := hs0.1.1.trans (le_csSup hSb hs0)
    have hat : a ≤ t := csSup_le ⟨s0, hs0⟩ (fun s hs => hs.1.2)
    have hafter : ∀ s, a < s → s ≤ t → c + d / 2 < v s := by
      intro s has hst
      by_contra hh
      push Not at hh
      have : s ≤ a := le_csSup hSb ⟨⟨ha0.trans has.le, hst⟩, hh⟩
      linarith
    by_cases hya : v a ≤ c + d / 2
    · apply compl_contra w G hint (Set.Ioc a t) measurableSet_Ioc
        (fun s hs => ha0.trans hs.1.le) (half_pos hd)
      · intro s hs
        have := hafter s hs.1 hs.2
        have := hzlow s ⟨ha0.trans hs.1.le, hs.2⟩
        linarith
      · rw [StieltjesFunction.measure_Ioc, hGa t ht, hGa a ha0]
        apply (ENNReal.ofReal_pos.2 _).ne'
        linarith
    · push Not at hya
      have hleft : Function.leftLim G a ≤ c + d / 2 := by
        have hm : Monotone G := G.mono
        apply le_of_tendsto (hm.tendsto_leftLim a)
        filter_upwards [self_mem_nhdsWithin] with s (hs : s < a)
        by_cases hs0' : 0 ≤ s
        · obtain ⟨s', hs'S, hss'⟩ := exists_lt_of_lt_csSup ⟨s0, hs0⟩ hs
          rw [hGa s hs0']
          exact (hvmono hs0' (hs0'.trans hss'.le) hss'.le).trans hs'S.2
        · rw [hG, if_neg hs0']; linarith
      apply compl_contra w G hint (Set.Icc a t) measurableSet_Icc
        (fun s hs => ha0.trans hs.1) (half_pos hd)
      · intro s hs
        have := hvmono ha0 (ha0.trans hs.1) hs.1
        have := hzlow s ⟨ha0.trans hs.1, hs.2⟩
        linarith
      · rw [StieltjesFunction.measure_Icc, hGa t ht]
        apply (ENNReal.ofReal_pos.2 _).ne'
        linarith
  · have hall : ∀ s ∈ Set.Icc 0 t, c + d / 2 < v s := by
      intro s hs
      by_contra hh
      push Not at hh
      exact hSne ⟨s, hs, hh⟩
    have hleft : Function.leftLim G 0 ≤ 0 := by
      have hm : Monotone G := G.mono
      apply le_of_tendsto (hm.tendsto_leftLim 0)
      filter_upwards [self_mem_nhdsWithin] with s (hs : s < 0)
      rw [hG, if_neg (not_le.2 hs)]
    apply compl_contra w G hint (Set.Icc 0 t) measurableSet_Icc
      (fun s hs => hs.1) (half_pos hd)
    · intro s hs
      have := hall s hs
      have := hzlow s hs
      linarith
    · rw [StieltjesFunction.measure_Icc, hGa t ht]
      apply (ENNReal.ofReal_pos.2 _).ne'
      have := hall t ⟨ht, le_rfl⟩
      linarith

end RBLem42Aux

open RBLem42Aux in
theorem solution (y x z : ℝ → ℝ) (hy : IsCadlag y) (hx : IsCadlag x) (hz : IsCadlag z)
    (hx0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ x t) (hz0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ z t)
    (hxyz : ∀ t : ℝ, 0 ≤ t → x t = y t + z t) :
    (MonotoneOn z (Set.Ici 0) ∧ StieltjesComplementary x z) ↔
      ∀ t : ℝ, 0 ≤ t → x t = y t + skorokhodReg y t ∧ z t = skorokhodReg y t := by
  constructor
  · rintro ⟨hm, hc⟩ t ht
    have h := skorokhod_unique' y hy x z hx0 hz0 hxyz hm hc ht
    exact ⟨by rw [hxyz t ht, h], h⟩
  · intro h
    refine ⟨fun a ha b hb hab => ?_, ?_⟩
    · rw [(h a ha).2, (h b hb).2]
      exact reg_mono y hy ha hb hab
    · obtain ⟨G, hGapp, hint⟩ := reg_compl y hy
      refine ⟨G, fun t => ?_, ?_⟩
      · rw [hGapp t]
        split_ifs with h0
        · rw [(h t h0).2]
        · rfl
      · rw [setLIntegral_congr_fun measurableSet_Ici (fun t ht => by rw [(h t ht).1])]
        exact hint
