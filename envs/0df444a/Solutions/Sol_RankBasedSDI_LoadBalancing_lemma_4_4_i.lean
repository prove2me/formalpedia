-- Prove2me | solution 1 for RankBasedSDI.LoadBalancing.lemma_4_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:05:55.354525+00:00
-- url     : https://prove2.me/submissions/85cb88ae-cb6a-40d7-af48-e7a10c9fb408

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
import Definitions.Def_RankBasedSDI_LoadBalancing_Model
import Definitions.Def_RankBasedSDI_LoadBalancing_ScaledProcesses
import Theorems.Thm_RankBasedSDI_LoadBalancing_lemma_4_2
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy
open RankBasedSDI.LoadBalancing

namespace RBL44Aux

/-- The positivity set of a path that is right-continuous on `[0, ∞)` is Borel. -/
lemma measurableSet_pos (x : ℝ → ℝ) (hx : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt x (Set.Ici t) t) :
    MeasurableSet {s : ℝ | 0 ≤ s ∧ 0 < x s} := by
  set U := {s : ℝ | 0 ≤ s ∧ 0 < x s}
  have hloc : ∀ s ∈ U, ∃ δ > 0, Set.Ico s (s + δ) ⊆ U := by
    intro s hs
    have h2 : ∀ᶠ y in 𝓝[≥] s, 0 < x y := (hx s hs.1).eventually (lt_mem_nhds hs.2)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h2
    refine ⟨u - s, by simpa using hu, fun r hr => ⟨hs.1.trans hr.1, hsub ?_⟩⟩
    simpa using hr
  choose! δ hδ hsub using hloc
  set O := ⋃ s ∈ U, Set.Ioo s (s + δ s)
  have hO : IsOpen O := isOpen_biUnion (fun _ _ => isOpen_Ioo)
  have hOU : O ⊆ U := by
    intro r hr
    simp only [O, Set.mem_iUnion] at hr
    obtain ⟨s, hs, hr⟩ := hr
    exact hsub s hs ⟨hr.1.le, hr.2⟩
  have hq : ∀ s ∈ U, ∃ q : ℚ, s < q ∧ (q : ℝ) < s + δ s := fun s hs =>
    exists_rat_btwn (by linarith [hδ s hs])
  choose! f hf using hq
  have hinj : Set.InjOn f (U \ O) := by
    have key : ∀ t ∈ U \ O, ∀ t' ∈ U \ O, t < t' → f t ≠ f t' := by
      intro t ht t' ht' htt' hfe
      have h1 := hf t ht.1
      have h2 := hf t' ht'.1
      apply ht'.2
      simp only [O, Set.mem_iUnion]
      refine ⟨t, ht.1, htt', ?_⟩
      have : (f t' : ℝ) = f t := by rw [hfe]
      linarith
    intro t ht t' ht' hfe
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key t ht t' ht' h hfe
    · exact key t' ht' t ht h hfe.symm
  have hcount : (U \ O).Countable :=
    Set.MapsTo.countable_of_injOn (Set.mapsTo_univ _ _) hinj Set.countable_univ
  have : U = O ∪ (U \ O) := by
    ext r; constructor
    · intro hr; by_cases h : r ∈ O
      · exact Or.inl h
      · exact Or.inr ⟨hr, h⟩
    · rintro (h | h)
      · exact hOU h
      · exact h.1
  rw [this]
  exact hO.measurableSet.union hcount.measurableSet

/-- `φ(t) = |(0,t] \ U|`, the idle-time function. -/
noncomputable def phi (U : Set ℝ) (t : ℝ) : ℝ := volume.real (Set.Ioc 0 t \ U)

lemma phi_nonneg (U : Set ℝ) (t : ℝ) : 0 ≤ phi U t := measureReal_nonneg

lemma phi_neg (U : Set ℝ) {t : ℝ} (ht : t ≤ 0) : phi U t = 0 := by
  unfold phi
  rw [Set.Ioc_eq_empty (not_lt.2 ht)]
  simp

lemma Ioc_diff_ne_top (U : Set ℝ) (b : ℝ) : volume (Set.Ioc 0 b \ U) ≠ ∞ :=
  ((measure_mono Set.diff_subset).trans_lt measure_Ioc_lt_top).ne

lemma phi_sub (U : Set ℝ) (hU : MeasurableSet U) {a b : ℝ} (hab : a ≤ b) :
    phi U b - phi U a = volume.real ((Set.Ioc 0 b \ U) \ (Set.Ioc 0 a \ U)) := by
  unfold phi
  have hA : MeasurableSet (Set.Ioc 0 a \ U) := measurableSet_Ioc.diff hU
  have h := measureReal_inter_add_sdiff (μ := volume) (s := Set.Ioc 0 b \ U) hA
    (Ioc_diff_ne_top U b)
  have hsub : (Set.Ioc 0 b \ U) ∩ (Set.Ioc 0 a \ U) = Set.Ioc 0 a \ U :=
    Set.inter_eq_right.2 (fun r hr => ⟨⟨hr.1.1, hr.1.2.trans hab⟩, hr.2⟩)
  rw [hsub] at h
  linarith

lemma phi_mono (U : Set ℝ) (hU : MeasurableSet U) : Monotone (phi U) := by
  intro a b hab
  have := phi_sub U hU hab
  have : 0 ≤ volume.real ((Set.Ioc 0 b \ U) \ (Set.Ioc 0 a \ U)) := measureReal_nonneg
  linarith

lemma phi_sub_le (U : Set ℝ) (hU : MeasurableSet U) {a b : ℝ} (hab : a ≤ b) :
    phi U b - phi U a ≤ b - a := by
  rw [phi_sub U hU hab]
  have hsub : (Set.Ioc 0 b \ U) \ (Set.Ioc 0 a \ U) ⊆ Set.Ioc a b := by
    rintro r ⟨⟨⟨h0, hb⟩, hU⟩, hn⟩
    refine ⟨?_, hb⟩
    by_contra h
    exact hn ⟨⟨h0, not_lt.1 h⟩, hU⟩
  calc _ ≤ volume.real (Set.Ioc a b) := measureReal_mono hsub measure_Ioc_lt_top.ne
    _ = b - a := by simp [hab]

lemma phi_continuous (U : Set ℝ) (hU : MeasurableSet U) : Continuous (phi U) := by
  have : LipschitzWith 1 (phi U) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total a b with h | h
    · have h1 := phi_sub_le U hU h
      have h2 := phi_mono U hU h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have h1 := phi_sub_le U hU h
      have h2 := phi_mono U hU h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  exact this.continuous

lemma phi_eq (U : Set ℝ) (hU : MeasurableSet U) {t : ℝ} (ht : 0 ≤ t) :
    phi U t = t - ∫ s in (0 : ℝ)..t, U.indicator (1 : ℝ → ℝ) s := by
  rw [intervalIntegral.integral_of_le ht, integral_indicator_one hU,
    measureReal_restrict_apply hU]
  unfold phi
  have := measureReal_inter_add_sdiff (μ := volume) (s := Set.Ioc (0 : ℝ) t) hU
    measure_Ioc_lt_top.ne
  rw [Real.volume_real_Ioc_of_le ht, sub_zero] at this
  rw [Set.inter_comm] at this
  linarith

/-- The Stieltjes function `t ↦ c φ(t)`. -/
noncomputable def phiG (U : Set ℝ) (hU : MeasurableSet U) (c : ℝ) (hc : 0 ≤ c) :
    StieltjesFunction ℝ where
  toFun := fun t => c * phi U t
  mono' := fun a b hab => mul_le_mul_of_nonneg_left (phi_mono U hU hab) hc
  right_continuous' := fun t =>
    ((continuous_const.mul (phi_continuous U hU)).continuousAt).continuousWithinAt

lemma phiG_apply (U : Set ℝ) (hU : MeasurableSet U) (c : ℝ) (hc : 0 ≤ c) (t : ℝ) :
    phiG U hU c hc t = c * phi U t := rfl

lemma set_eq_aux (U : Set ℝ) {a b : ℝ} (hab : a < b) :
    (Set.Ioc 0 b \ U) \ (Set.Ioc 0 a \ U) = Set.Ioc a b ∩ (Set.Ioi 0 \ U) := by
  ext r
  simp only [Set.mem_diff, Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨⟨h0, hb⟩, hU⟩, hn⟩
    refine ⟨⟨?_, hb⟩, h0, hU⟩
    by_contra h
    exact hn ⟨⟨h0, not_lt.1 h⟩, hU⟩
  · rintro ⟨⟨ha, hb⟩, h0, hU⟩
    exact ⟨⟨⟨h0, hb⟩, hU⟩, fun h => absurd h.1.2 (not_le.2 ha)⟩

lemma phiG_measure (U : Set ℝ) (hU : MeasurableSet U) (c : ℝ) (hc : 0 ≤ c) :
    (phiG U hU c hc).measure = ENNReal.ofReal c • volume.restrict (Set.Ioi 0 \ U) := by
  refine Measure.ext_of_Ioc _ _ (fun a b hab => ?_)
  rw [StieltjesFunction.measure_Ioc, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
    smul_eq_mul, phiG_apply, phiG_apply, ← mul_sub, phi_sub U hU hab.le, set_eq_aux U hab,
    ENNReal.ofReal_mul hc, measureReal_def, ENNReal.ofReal_toReal]
  exact ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top).ne

end RBL44Aux

open RBL44Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) (n : ℕ) (i : Fin N) :
    ∀ᵐ ω ∂S.P,
      (∀ t : ℝ, 0 ≤ t → Xhat S n ω t i = Uhat H n ω t i + Lhat S n ω t i) ∧
      IsC0Up (fun t => Lhat S n ω t i) ∧
      StieltjesComplementary (fun t => Xhat S n ω t i) (fun t => Lhat S n ω t i) ∧
      (∀ t : ℝ, 0 ≤ t →
        Xhat S n ω t i = Uhat H n ω t i + skorokhodReg (fun s => Uhat H n ω s i) t ∧
        Lhat S n ω t i = skorokhodReg (fun s => Uhat H n ω s i) t) := by
  filter_upwards [S.balance n i, S.busy n i, S.departures n i] with ω hbal hbusy hdep
  have hxc := S.X_cadlag n i ω
  set U := {s : ℝ | 0 ≤ s ∧ 0 < S.X n i ω s} with hUdef
  have hU : MeasurableSet U := measurableSet_pos _ hxc.1
  have hT : ∀ t, 0 ≤ t → S.T n i ω t = t - phi U t := by
    intro t ht
    rw [hbusy t ht, phi_eq U hU ht]
    have : ∫ s in (0:ℝ)..t, (if 0 < S.X n i ω s then (1:ℝ) else 0) =
        ∫ s in (0:ℝ)..t, U.indicator 1 s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      simp [U, Set.indicator, hs.1]
    rw [this]; ring
  set c := S.mu n i / Real.sqrt n with hcdef
  have hc : 0 ≤ c := div_nonneg (S.mu_pos n i).le (Real.sqrt_nonneg _)
  have hL : ∀ t, 0 ≤ t → Lhat S n ω t i = c * phi U t := by
    intro t ht
    simp only [Lhat, c]
    rw [hT t ht]; ring
  have hdecomp : ∀ t, 0 ≤ t → Xhat S n ω t i = Uhat H n ω t i + Lhat S n ω t i := by
    intro t ht
    simp only [Xhat, Uhat, Lhat, Xhat0, Ehat, Ahat, Shat, mhatN]
    have h1 := hbal t ht
    have h2 := hdep t ht
    have h3 := H.critical i
    simp only [div_eq_mul_inv]
    rw [h1, h2, h3]; ring
  have hLC0 : IsC0Up (fun t => Lhat S n ω t i) := by
    refine ⟨ContinuousOn.congr (continuous_const.mul (phi_continuous U hU)).continuousOn
      (fun t ht => hL t ht), fun a ha b hb hab => ?_, ?_⟩
    · simp only
      rw [hL a ha, hL b hb]
      exact mul_le_mul_of_nonneg_left (phi_mono U hU hab) hc
    · simp only
      rw [hL 0 le_rfl, phi_neg U le_rfl, mul_zero]
  have hcompl : StieltjesComplementary (fun t => Xhat S n ω t i) (fun t => Lhat S n ω t i) := by
    refine ⟨phiG U hU c hc, fun t => ?_, ?_⟩
    · rw [phiG_apply]
      split_ifs with ht
      · exact (hL t ht).symm
      · rw [phi_neg U (le_of_lt (not_le.1 ht)), mul_zero]
    · rw [phiG_measure, Measure.restrict_smul, lintegral_smul_measure]
      have : ∀ᵐ t ∂((volume.restrict (Set.Ioi 0 \ U)).restrict (Set.Ici 0)),
          ENNReal.ofReal (Xhat S n ω t i) = 0 := by
        apply ae_restrict_of_ae
        rw [ae_restrict_iff' (measurableSet_Ioi.diff hU)]
        refine Eventually.of_forall (fun s hs => ?_)
        have hns : ¬ (0 < S.X n i ω s) := fun h => hs.2 ⟨le_of_lt hs.1, h⟩
        apply ENNReal.ofReal_eq_zero.2
        simp only [Xhat]
        exact div_nonpos_of_nonpos_of_nonneg (not_lt.1 hns) (Real.sqrt_nonneg _)
      rw [lintegral_congr_ae this, lintegral_zero, smul_zero]
  have hXc : IsCadlag (fun t => Xhat S n ω t i) := by
    simp only [Xhat]
    refine ⟨fun t ht => (hxc.1 t ht).div_const _, fun t ht => ?_⟩
    obtain ⟨l, hl⟩ := hxc.2 t ht
    exact ⟨l / Real.sqrt n, hl.div_const _⟩
  have hLc : IsCadlag (fun t => Lhat S n ω t i) := by
    refine ⟨fun t ht => (hLC0.1 t ht).mono (Set.Ici_subset_Ici.2 ht), fun t ht => ?_⟩
    have hca := (hLC0.1 t ht.le).continuousAt (Ici_mem_nhds ht)
    exact ⟨_, hca.tendsto.mono_left nhdsWithin_le_nhds⟩
  have hUeq : ∀ s, 0 ≤ s → Uhat H n ω s i = Xhat S n ω s i - Lhat S n ω s i := by
    intro s hs; have := hdecomp s hs; linarith
  have hUc : IsCadlag (fun t => Uhat H n ω t i) := by
    refine ⟨fun t ht => ((hXc.1 t ht).sub (hLc.1 t ht)).congr
      (fun s hs => hUeq s (ht.trans hs)) (hUeq t ht), fun t ht => ?_⟩
    obtain ⟨l1, h1⟩ := hXc.2 t ht
    obtain ⟨l2, h2⟩ := hLc.2 t ht
    refine ⟨l1 - l2, (h1.sub h2).congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact (hUeq s hs.1.le).symm
  have hX0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Xhat S n ω t i := by
    intro t ht
    obtain ⟨k, hk⟩ := S.X_nat n i ω t ht
    simp only [Xhat, hk]
    positivity
  have hL0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Lhat S n ω t i := by
    intro t ht
    rw [hL t ht]
    exact mul_nonneg hc (phi_nonneg U t)
  have h42 := (lemma_4_2 (fun t => Uhat H n ω t i) (fun t => Xhat S n ω t i)
    (fun t => Lhat S n ω t i) hUc hXc hLc hX0 hL0 hdecomp).1 ⟨hLC0.2.1, hcompl⟩
  exact ⟨hdecomp, hLC0, hcompl, h42⟩
