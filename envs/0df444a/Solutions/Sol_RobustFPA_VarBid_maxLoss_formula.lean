-- Prove2me | solution 1 for RobustFPA.VarBid.maxLoss_formula
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T01:57:29.94999+00:00
-- url     : https://prove2.me/submissions/74bdadfc-ba79-4d20-9ef0-26dafed851cf

/- Completion of the full maximal-loss formula from the earlier checked local supporting lemmas. Boundary-support and supremum arguments: Alexander Richard Towell (direction), OpenAI Codex (formalization). Source and earlier attribution are retained below. -/
/-
Local checked support for the corrected robust first-price auction model.
Alexander Richard Towell (queelius): direction and stewardship.
OpenAI Codex: substantial formalization, verification and documentation.
Original mathematics: Bernhard Kasberger and Karl Schlag, Robust Bidding in
First-Price Auctions. The platform cites 3 September 2022; the inspected author
PDF is dated 27 March 2023, pp.20–22. This source-version limitation is retained.
mikedeng1 supplied the platform model and explicit ambiguity-set repair;
Shuze Chen's statement confirmation is distinct from proof review.
Lean and Mathlib supply measure, integration and algebra foundations.
No predecessor platform proof body is used here. This establishes common-law
integrals, admissibility and lower bounds, not the full minimax theorem.
No mathematical novelty or independent human proof review is claimed.
-/
import Mathlib
import Definitions.Def_RobustFPA_VarBid_Model
import Definitions.Def_RobustFPA_VarBid_AmbiguitySet
import Definitions.Def_RobustFPA_VarBid_ClosedForms

open MeasureTheory
open scoped ENNReal
namespace RobustFPA.VarBid

lemma uniform_probability (L v : ℝ) (hLv : L < v) : IsProbabilityMeasure (uniformG L v) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hLv))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

lemma uniform_lower_support (L v : ℝ) : uniformG L v (Set.Iio L) = 0 := by
  have h : Set.Icc L v ∩ Set.Iio L = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_ge hx.1.1) hx.2
  unfold uniformG
  rw [ProbabilityTheory.cond_apply' measurableSet_Iio, h]
  simp

lemma common_admissible (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (x : ℝ) (hx : L ≤ x) :
    commonBidEnv n τ (uniformG L v) x ∈ varBidSet n τ L (uniformG L v) := by
  refine ⟨hn, hL, hτ0.le, hτ1.le, uniform_probability L v hLv,
    uniform_lower_support L v, Measure.dirac (fun _ => x), inferInstance, ?_, rfl⟩
  simp [Measure.dirac_apply', hx]

lemma bern_probability (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    IsProbabilityMeasure (bern τ) := by
  constructor
  simp only [bern, Measure.add_apply, MeasurableSet.univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  simp only [ENNReal.smul_one]
  rw [← ENNReal.coe_add, ← Real.toNNReal_add hτ0]
  · simp
  · linarith

lemma measurable_mix {m : ℕ} :
    Measurable (fun p : (Fin m → Bool × ℝ) × (Fin m → ℝ) => mixBids p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  unfold mixBids
  exact Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

lemma common_law (n : ℕ) (τ : ℝ) (G : Measure ℝ) [IsFiniteMeasure G] (x : ℝ) :
    commonBidEnv n τ G x =
      (constrainedLaw (n-1) τ G).map (fun cy j => if (cy j).1 then (cy j).2 else x) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  letI : IsFiniteMeasure (constrainedLaw (n-1) τ G) := by unfold constrainedLaw; infer_instance
  unfold commonBidEnv envOf
  rw [Measure.prod_dirac, Measure.map_map measurable_mix (by fun_prop)]
  rfl

lemma component_law (τ x : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G] :
    ((bern τ).prod G).map (fun p : Bool × ℝ => if p.1 then p.2 else x) =
      Real.toNNReal τ • G + Real.toNNReal (1-τ) • Measure.dirac x := by
  have hm : Measurable (fun p : Bool × ℝ => if p.1 then p.2 else x) := by
    exact Measurable.ite (by measurability) measurable_snd measurable_const
  unfold bern
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map hm measurable_prodMk_left, Measure.map_map hm measurable_prodMk_left]
  simp [Function.comp_def]

lemma common_product (n : ℕ) (τ : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G] (x : ℝ) :
    commonBidEnv n τ G x = Measure.pi (fun _ : Fin (n-1) =>
      Real.toNNReal τ • G + Real.toNNReal (1-τ) • Measure.dirac x) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  rw [common_law]
  unfold constrainedLaw
  have hm : Measurable (fun p : Bool × ℝ => if p.1 then p.2 else x) := by
    exact Measurable.ite (by measurability) measurable_snd measurable_const
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  simp_rw [component_law]

lemma uniform_noatoms (L v : ℝ) : NullSingletonClass (uniformG L v) := by
  constructor
  intro x
  unfold uniformG
  rw [ProbabilityTheory.cond_apply' (measurableSet_singleton x)]
  have h : (volume : Measure ℝ) (Set.Icc L v ∩ {x}) = 0 :=
    measure_mono_null Set.inter_subset_right (measure_singleton x)
  simp [h]

lemma uniform_Iio (L v b : ℝ) (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) :
    uniformG L v (Set.Iio b) = ENNReal.ofReal ((b-L)/(v-L)) := by
  have hi : Set.Icc L v ∩ Set.Iio b = Set.Ico L b := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.le.trans hbv⟩, h.2⟩
  unfold uniformG
  rw [ProbabilityTheory.cond_apply' measurableSet_Iio, hi, Real.volume_Icc, Real.volume_Ico]
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hLv)]
  rw [div_eq_mul_inv, mul_comm]

lemma product_payoff (m : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v b : ℝ) (hμ : μ {b} = 0) :
    expUtil v b (Measure.pi (fun _ : Fin m => μ)) =
      (μ (Set.Iio b)).toReal ^ m * (v-b) := by
  classical
  let S : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Set.Iio b)
  have hs : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Iio)
  have hn : ∀ᵐ o ∂Measure.pi (fun _ : Fin m => μ), ∀ j, o j ≠ b := by
    rw [ae_all_iff]
    intro j
    apply ae_iff.mpr
    simpa only [not_not, Set.preimage, Set.mem_singleton_iff, Function.eval] using
      (Measure.pi_eval_preimage_null (fun _ : Fin m => μ) (i := j) hμ)
  have he : (fun o => payoff v b o) =ᵐ[Measure.pi (fun _ : Fin m => μ)]
      S.indicator (fun _ => v-b) := by
    filter_upwards [hn] with o ho
    by_cases hw : ∀ j, o j ≤ b
    · have hm : o ∈ S := by
        simpa [S, Set.mem_pi] using (fun j => lt_of_le_of_ne (hw j) (ho j))
      have hf : (Finset.univ.filter (fun j => o j = b)) = ∅ := by
        ext j
        simp [ho j]
      simp [payoff, hw, hf, Set.indicator_of_mem hm]
    · have hm : o ∉ S := by
        intro h
        have hh : ∀ j, o j < b := by simpa [S, Set.mem_pi] using h
        exact hw (fun j => (hh j).le)
      simp [payoff, hw, Set.indicator_of_notMem hm]
  unfold expUtil
  rw [integral_congr_ae he, integral_indicator_const _ hs]
  simp only [Measure.real, S, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow, smul_eq_mul]

lemma common_no_tie (τ L v b x : ℝ) (hxb : x ≠ b) :
    (Real.toNNReal τ • uniformG L v + Real.toNNReal (1-τ) • Measure.dirac x) {b} = 0 := by
  letI := uniform_noatoms L v
  simp [hxb]

lemma common_utility (n : ℕ) (τ L v b x : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (hxb : x ≠ b) :
    expUtil v b (commonBidEnv n τ (uniformG L v) x) =
      (τ * ((b-L)/(v-L)) + if x < b then 1-τ else 0) ^ (n-1) * (v-b) := by
  letI := uniform_probability L v hLv
  rw [common_product, product_payoff _ _ _ _ (common_no_tie τ L v b x hxb)]
  congr 2
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, uniform_Iio L v b hLv hLb hbv]
  have hratio : 0 ≤ (b-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLb) (sub_pos.mpr hLv).le
  simp [ENNReal.toReal_ofReal hratio, Real.toNNReal_of_nonneg hτ0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hτ1), Measure.dirac_apply']
  by_cases hx : x < b <;> simp [Set.indicator, hx]

lemma common_utility_above (n : ℕ) (τ L v b x : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (hxb : x < b) :
    expUtil v b (commonBidEnv n τ (uniformG L v) x) = uPlus n τ L v b := by
  rw [common_utility n τ L v b x hτ0 hτ1 hLv hLb hbv hxb.ne]
  simp only [if_pos hxb, uPlus]
  ring

lemma common_utility_below (n : ℕ) (τ L v b x : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (hbx : b < x) :
    expUtil v b (commonBidEnv n τ (uniformG L v) x) = uMinus n τ L v b := by
  rw [common_utility n τ L v b x hτ0 hτ1 hLv hLb hbv hbx.ne']
  simp [not_lt_of_ge hbx.le, uMinus]

lemma payoff_measurable (m : ℕ) (v b : ℝ) : Measurable (payoff (m := m) v b) := by
  classical
  have hc : Measurable (fun o : Fin m → ℝ =>
      ((Finset.univ.filter (fun j => o j = b)).card : ℝ)) := by
    have hh : Measurable (fun o : Fin m → ℝ =>
        ∑ j : Fin m, if o j = b then (1:ℝ) else 0) := by
      apply Finset.measurable_sum
      intro j _
      exact Measurable.ite (by measurability) measurable_const measurable_const
    simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh
  unfold payoff
  exact Measurable.ite (by measurability) (measurable_const.div (hc.add_const 1)) measurable_const

lemma payoff_bound (m : ℕ) (v b : ℝ) (o : Fin m → ℝ) :
    ‖payoff v b o‖ ≤ |v-b| := by
  classical
  unfold payoff
  split_ifs
  · have hd : (1:ℝ) ≤ ((Finset.univ.filter (fun j => o j = b)).card : ℝ) + 1 := by have h := Nat.cast_nonneg (α := ℝ) (Finset.univ.filter (fun j => o j = b)).card; linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr (by nlinarith [abs_nonneg (v-b)])
  · simp

lemma payoff_integrable (m : ℕ) (v b : ℝ) (B : Measure (Fin m → ℝ)) [IsFiniteMeasure B] :
    Integrable (payoff v b) B := by
  apply Integrable.mono' (integrable_const |v-b|) (payoff_measurable m v b).aestronglyMeasurable
  exact Filter.Eventually.of_forall (payoff_bound m v b)

lemma environment_probability (n : ℕ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    IsProbabilityMeasure (envOf n τ G H) := by
  letI := bern_probability τ hτ0 hτ1
  letI : IsProbabilityMeasure (constrainedLaw (n-1) τ G) := by
    unfold constrainedLaw
    infer_instance
  exact Measure.isProbabilityMeasure_map measurable_mix.aemeasurable

lemma admissible_probability (n : ℕ) (τ L : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L G) :
    IsProbabilityMeasure B := by
  rcases hB with ⟨_, _, hτ0, hτ1, hG, _, H, hH, _, rfl⟩
  letI := hG
  letI := hH
  exact environment_probability n τ hτ0 hτ1 G H

lemma payoff_le_value (m : ℕ) (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b) (o : Fin m → ℝ) :
    payoff v b o ≤ v := by
  classical
  unfold payoff
  split_ifs
  · have hc : 0 ≤ ((Finset.univ.filter (fun j => o j = b)).card : ℝ) := Nat.cast_nonneg _
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · exact hv

lemma expUtil_le_value (m : ℕ) (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (B : Measure (Fin m → ℝ)) [IsProbabilityMeasure B] : expUtil v b B ≤ v := by
  have h := integral_mono (payoff_integrable m v b B) (integrable_const v)
    (payoff_le_value m v b hv hb)
  simpa [expUtil] using h

lemma bestUtil_bounds (m : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (B : Measure (Fin m → ℝ)) [IsProbabilityMeasure B] :
    0 ≤ bestUtil v B ∧ bestUtil v B ≤ v := by
  have hB : BddAbove ((fun b => expUtil v b B) '' Set.Ici 0) := by
    refine ⟨v, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact expUtil_le_value m v b hv hb B
  have hzero : expUtil v v B = 0 := by simp [expUtil, payoff]
  constructor
  · have hh : expUtil v v B ≤ bestUtil v B := le_csSup hB ⟨v, hv, rfl⟩
    simpa only [hzero] using hh
  · have hn : ((fun b : ℝ => expUtil v b B) '' Set.Ici 0).Nonempty :=
      ⟨expUtil v 0 B, 0, by simp, rfl⟩
    exact csSup_le hn (by rintro _ ⟨b, hb, rfl⟩; exact expUtil_le_value m v b hv hb B)

lemma expUtil_lower (m : ℕ) (v b : ℝ) (B : Measure (Fin m → ℝ)) [IsProbabilityMeasure B] :
    -|v-b| ≤ expUtil v b B := by
  have hp : ∀ o : Fin m → ℝ, -|v-b| ≤ payoff v b o := by
    intro o
    have h := payoff_bound m v b o
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  have h := integral_mono (integrable_const (-|v-b|)) (payoff_integrable m v b B) hp
  simpa [expUtil] using h

lemma losses_bounded (n : ℕ) (τ L v b : ℝ) (hv : 0 ≤ v)
    (G : Measure ℝ) [IsFiniteMeasure G] :
    BddAbove ((fun B => loss v b B) '' varBidSet n τ L G) := by
  refine ⟨v+|v-b|, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  letI := admissible_probability n τ L G B hB
  have hu := (bestUtil_bounds (n-1) v hv B).2
  have hl := expUtil_lower (n-1) v b B
  unfold loss
  linarith

lemma common_gain_le_maxLoss (n : ℕ) (hn : 2 ≤ n) (τ L v b h x : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hh : 0 ≤ h) (hx : L ≤ x) :
    expUtil v h (commonBidEnv n τ (uniformG L v) x) -
      expUtil v b (commonBidEnv n τ (uniformG L v) x) ≤
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  have hB := common_admissible n hn τ L v hτ0 hτ1 hL hLv x hx
  let B := commonBidEnv n τ (uniformG L v) x
  letI : IsProbabilityMeasure B := admissible_probability n τ L (uniformG L v) B hB
  have hv : 0 ≤ v := hL.trans hLv.le
  have hu : BddAbove ((fun z => expUtil v z B) '' Set.Ici 0) := by
    refine ⟨v, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact expUtil_le_value (n-1) v z hv hz B
  have hb : expUtil v h B ≤ bestUtil v B := le_csSup hu ⟨h, hh, rfl⟩
  have hl : loss v b B ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) :=
    le_csSup (losses_bounded n τ L v b hv (uniformG L v)) ⟨B, hB, rfl⟩
  exact (sub_le_sub_right hb _).trans hl

lemma low_gain_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbh : b < h) (hhv : h ≤ v) :
    uPlus n τ L v h - uMinus n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  let x := (b+h)/2
  have hbx : b < x := by dsimp [x]; linarith
  have hxh : x < h := by dsimp [x]; linarith
  have q := common_gain_le_maxLoss n hn τ L v b h x hτ0 hτ1 hL hLv
    (hL.trans (hLb.trans hbh.le)) (hLb.trans hbx.le)
  rw [common_utility_above n τ L v h x hτ0.le hτ1.le hLv (hLb.trans hbh.le) hhv hxh,
    common_utility_below n τ L v b x hτ0.le hτ1.le hLv hLb (hbh.le.trans hhv) hbx] at q
  exact q

lemma high_gain_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLh : L < h) (hhb : h ≤ b) (hbv : b ≤ v) :
    uPlus n τ L v h - uPlus n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  let x := (L+h)/2
  have hLx : L < x := by dsimp [x]; linarith
  have hxh : x < h := by dsimp [x]; linarith
  have q := common_gain_le_maxLoss n hn τ L v b h x hτ0 hτ1 hL hLv
    (hL.trans hLh.le) hLx.le
  rw [common_utility_above n τ L v h x hτ0.le hτ1.le hLv hLh.le (hhb.trans hbv) hxh,
    common_utility_above n τ L v b x hτ0.le hτ1.le hLv (hLh.le.trans hhb) hbv (hxh.trans_le hhb)] at q
  exact q


lemma payoff_nonnegative {m : ℕ} (v b : ℝ) (hbv : b ≤ v) (o : Fin m → ℝ) :
    0 ≤ payoff v b o := by
  unfold payoff
  split_ifs <;> positivity

lemma mixed_payoff_lower {m : ℕ} (v b x : ℝ) (hbv : b ≤ v) (hbx : b < x)
    (cy : Fin m → Bool × ℝ) (z : Fin m → ℝ) :
    payoff v b (mixBids cy (fun _ => x)) ≤ payoff v b (mixBids cy z) := by
  classical
  by_cases hw : ∀ j, mixBids cy (fun _ => x) j ≤ b
  · have hall : ∀ j, (cy j).1 = true := by
      intro j
      have h := hw j
      unfold mixBids at h
      cases hc : (cy j).1
      · simp [hc] at h
        linarith
      · rfl
    have he : mixBids cy (fun _ => x) = mixBids cy z := by
      funext j
      simp [mixBids, hall j]
    rw [he]
  · rw [payoff, if_neg hw]
    exact payoff_nonnegative v b hbv _

lemma mixed_payoff_upper {m : ℕ} (v b x : ℝ) (hbv : b ≤ v) (hxb : x < b)
    (cy : Fin m → Bool × ℝ) (z : Fin m → ℝ) :
    payoff v b (mixBids cy z) ≤ payoff v b (mixBids cy (fun _ => x)) := by
  classical
  by_cases hw : ∀ j, mixBids cy z j ≤ b
  · have hw' : ∀ j, mixBids cy (fun _ => x) j ≤ b := by
      intro j
      have h := hw j
      unfold mixBids at h ⊢
      split_ifs with hc
      · simpa [hc] using h
      · exact hxb.le
    have hsub : (Finset.univ.filter (fun j => mixBids cy (fun _ => x) j = b)) ⊆
        (Finset.univ.filter (fun j => mixBids cy z j = b)) := by
      intro j hj
      have hh := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold mixBids at hh ⊢
      split_ifs with hc
      · simpa [hc] using hh
      · exact False.elim (hxb.ne (by simpa [hc] using hh))
    have hc := Finset.card_le_card hsub
    have hcr : ((Finset.univ.filter (fun j => mixBids cy (fun _ => x) j = b)).card : ℝ) ≤
      ((Finset.univ.filter (fun j => mixBids cy z j = b)).card : ℝ) := by exact_mod_cast hc
    simp only [payoff, if_pos hw, if_pos hw']
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hbv) (by positivity) (by linarith)
  · rw [payoff, if_neg hw]
    exact payoff_nonnegative v b hbv _

lemma mixed_integrable {m : ℕ} (v b : ℝ) (F : ((Fin m → Bool × ℝ) × (Fin m → ℝ)) → (Fin m → ℝ))
    (hF : Measurable F) (μ : Measure ((Fin m → Bool × ℝ) × (Fin m → ℝ))) [IsFiniteMeasure μ] :
    Integrable (fun p => payoff v b (F p)) μ := by
  apply Integrable.mono' (integrable_const |v-b|)
    ((payoff_measurable m v b).comp hF).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => payoff_bound m v b (F p))

lemma environment_integral (n : ℕ) (τ v b : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (H : Measure (Fin (n-1) → ℝ)) :
    expUtil v b (envOf n τ G H) =
      ∫ p, payoff v b (mixBids p.1 p.2) ∂((constrainedLaw (n-1) τ G).prod H) := by
  unfold expUtil envOf
  exact integral_map_of_stronglyMeasurable measurable_mix (payoff_measurable _ v b).stronglyMeasurable

set_option synthInstance.maxHeartbeats 200000 in
lemma common_integral (n : ℕ) (τ v b x : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    (∫ p, payoff v b (mixBids p.1 (fun _ => x)) ∂((constrainedLaw (n-1) τ G).prod H)) =
      expUtil v b (commonBidEnv n τ G x) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  letI : IsFiniteMeasure (constrainedLaw (n-1) τ G) := by unfold constrainedLaw; infer_instance
  rw [integral_fun_fst (μ := constrainedLaw (n-1) τ G) (ν := H)
    (fun cy => payoff v b (mixBids cy (fun _ => x)))]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [common_law]
  unfold expUtil
  symm
  apply integral_map_of_stronglyMeasurable
  · apply measurable_pi_lambda
    intro j
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  · exact (payoff_measurable _ v b).stronglyMeasurable

lemma environment_utility_bounds (n : ℕ) (τ L v b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v)
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    uMinus n τ L v b ≤ expUtil v b (envOf n τ (uniformG L v) H) ∧
    expUtil v b (envOf n τ (uniformG L v) H) ≤ uPlus n τ L v b := by
  letI := bern_probability τ hτ0 hτ1
  letI := uniform_probability L v hLv
  letI : IsProbabilityMeasure (constrainedLaw (n-1) τ (uniformG L v)) := by
    unfold constrainedLaw
    infer_instance
  let μ := (constrainedLaw (n-1) τ (uniformG L v)).prod H
  have hi := mixed_integrable v b (fun p => mixBids p.1 p.2) measurable_mix μ
  have hix (x : ℝ) := mixed_integrable v b (fun p => mixBids p.1 (fun _ => x))
    (by apply measurable_pi_lambda; intro j; exact Measurable.ite (by measurability) (by fun_prop) measurable_const) μ
  rw [environment_integral]
  constructor
  · have hh := integral_mono (hix (b+1)) hi (fun p => mixed_payoff_lower v b (b+1) hbv (by linarith) p.1 p.2)
    change (∫ p, payoff v b (mixBids p.1 (fun _ => b+1)) ∂μ) ≤ _ at hh
    rw [common_integral, common_utility_below n τ L v b (b+1) hτ0 hτ1 hLv hLb hbv (by linarith)] at hh
    exact hh
  · have hh := integral_mono hi (hix (b-1)) (fun p => mixed_payoff_upper v b (b-1) hbv (by linarith) p.1 p.2)
    change _ ≤ (∫ p, payoff v b (mixBids p.1 (fun _ => b-1)) ∂μ) at hh
    rw [common_integral, common_utility_above n τ L v b (b-1) hτ0 hτ1 hLv hLb hbv (by linarith)] at hh
    exact hh

lemma admissible_utility_bounds (n : ℕ) (τ L v b : ℝ) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    uMinus n τ L v b ≤ expUtil v b B ∧ expUtil v b B ≤ uPlus n τ L v b := by
  rcases hB with ⟨_, _, hτ0, hτ1, _, _, H, hH, _, rfl⟩
  letI := hH
  exact environment_utility_bounds n τ L v b hτ0 hτ1 hLv hLb hbv H

lemma deviation_upper (n : ℕ) (τ L v b h : ℝ) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) (hLh : L ≤ h) (hhv : h ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    expUtil v h B - expUtil v b B ≤ uPlus n τ L v h - uMinus n τ L v b := by
  exact sub_le_sub (admissible_utility_bounds n τ L v h hLv hLh hhv B hB).2
    (admissible_utility_bounds n τ L v b hLv hLb hbv B hB).1

lemma high_gain_closed (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLh : L ≤ h) (hhb : h ≤ b) (hbv : b ≤ v) :
    uPlus n τ L v h - uPlus n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  by_cases hLb : L < b
  · have hx : h ∈ closure (Set.Ioc L b) := by
      rw [closure_Ioc hLb.ne]
      exact ⟨hLh, hhb⟩
    have hc : Continuous (fun y => uPlus n τ L v y - uPlus n τ L v b) := by
      unfold uPlus
      fun_prop
    exact ContinuousWithinAt.closure_le hx hc.continuousWithinAt continuousWithinAt_const
      (fun y hy => high_gain_lower_bound n hn τ L v b y hτ0 hτ1 hL hLv hy.1 hy.2 hbv)
  · have he : h = b := by linarith
    have hlb : L ≤ b := hLh.trans hhb
    have hh := common_gain_le_maxLoss n hn τ L v b b L hτ0 hτ1 hL hLv (hL.trans hlb) le_rfl
    simpa [he] using hh

lemma tooHigh_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) :
    tooHigh n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  unfold tooHigh
  apply sub_le_iff_le_add.mpr
  apply csSup_le
  · exact ⟨uPlus n τ L v L, L, ⟨le_rfl, hLb⟩, rfl⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact (sub_le_iff_le_add.mp (high_gain_closed n hn τ L v b h hτ0 hτ1 hL hLv hh.1 hh.2 hbv))

lemma maxLoss_nonnegative (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) (hb : 0 ≤ b) :
    0 ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  simpa using common_gain_le_maxLoss n hn τ L v b b L hτ0 hτ1 hL hLv hb le_rfl

lemma tooLow_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) :
    tooLow n τ L v b ≤ maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  unfold tooLow
  apply sub_le_iff_le_add.mpr
  apply csSup_le
  · refine ⟨uPlus n τ L v (b+1), b+1, ?_, rfl⟩
    simp
  · rintro _ ⟨h, hh, rfl⟩
    apply sub_le_iff_le_add.mp
    by_cases hhv : h ≤ v
    · exact low_gain_lower_bound n hn τ L v b h hτ0 hτ1 hL hLv hLb hh hhv
    · have hp : uPlus n τ L v h ≤ 0 := by
        unfold uPlus
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
        have hhL : 0 ≤ h-L := by linarith [hh]
        have ht : 0 ≤ 1-τ := by linarith
        positivity
      have hm : 0 ≤ uMinus n τ L v b := by
        unfold uMinus
        have hbL : 0 ≤ b-L := sub_nonneg.mpr hLb
        have hvb : 0 ≤ v-b := sub_nonneg.mpr hbv
        positivity
      have hz := maxLoss_nonnegative n hn τ L v b hτ0 hτ1 hL hLv (hL.trans hLb)
      linarith

lemma analytic_max_lower_bound (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v)
    (hLb : L ≤ b) (hbv : b ≤ v) :
    max (tooHigh n τ L v b) (tooLow n τ L v b) ≤
      maxLoss v b (varBidSet n τ L (uniformG L v)) := by
  exact max_le (tooHigh_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)
    (tooLow_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)

end RobustFPA.VarBid

namespace RobustFPA.VarBid

/-- Preserve the common-law dependence through coordinatewise CDF ratios. -/
lemma product_gain_bound {ι : Type*} [Fintype ι] (a c : ι → ℝ)
    (A C r s : ℝ) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 ≤ r)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (hcC : ∀ i, c i ≤ C) (hcross : ∀ i, a i * C ≤ A * c i) :
    r * (∏ i, a i) - s * (∏ i, c i) ≤
      max (r * A ^ Fintype.card ι - s * C ^ Fintype.card ι) 0 := by
  classical
  let t := A / C
  have ht : 0 ≤ t := div_nonneg hA hC.le
  have hratio : ∀ i, a i ≤ t * c i := by
    intro i
    change a i ≤ (A / C) * c i
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hC).mpr (hcross i)
  have hp : (∏ i, a i) ≤ t ^ Fintype.card ι * ∏ i, c i := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => ha i) (fun i _ => hratio i)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h
  have hc0 : 0 ≤ ∏ i, c i := Finset.prod_nonneg (fun i _ => hc i)
  have hpc : (∏ i, c i) ≤ C ^ Fintype.card ι := by
    have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => hc i) (fun i _ => hcC i)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  have he : t ^ Fintype.card ι * C ^ Fintype.card ι = A ^ Fintype.card ι := by
    dsimp [t]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hC.ne')]
  have hgain : r * (∏ i, a i) - s * (∏ i, c i) ≤
      (r * t ^ Fintype.card ι - s) * ∏ i, c i := by
    nlinarith [mul_le_mul_of_nonneg_left hp hr]
  by_cases hsign : 0 ≤ r * t ^ Fintype.card ι - s
  · have h := mul_le_mul_of_nonneg_left hpc hsign
    have hh : (r * t ^ Fintype.card ι - s) * C ^ Fintype.card ι =
        r * A ^ Fintype.card ι - s * C ^ Fintype.card ι := by rw [sub_mul, mul_assoc, he]
    rw [hh] at h
    exact (hgain.trans h).trans (le_max_left _ _)
  · exact (hgain.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) hc0)).trans
      (le_max_right _ _)

/-- With heterogeneous unconstrained bids, each opponent has a low or high CDF factor. -/
lemma binary_product_gain_bound {ι : Type*} [Fintype ι] (low : ι → Bool)
    (τ p q r s : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 ≤ r) :
    r * (∏ i, (τ * p + if low i then 1 - τ else 0)) -
      s * (∏ i, (τ * q + if low i then 1 - τ else 0)) ≤
      max (r * (1 - τ + τ * p) ^ Fintype.card ι -
        s * (1 - τ + τ * q) ^ Fintype.card ι) 0 := by
  have hq : 0 ≤ q := hp.trans hpq
  apply product_gain_bound _ _ (1 - τ + τ * p) (1 - τ + τ * q) r s
    (by positivity) (by positivity) hr
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  · intro i
    cases low i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hpq)]
    · nlinarith

noncomputable def favorableProjection {m : ℕ} (h b : ℝ) (z : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if z i ≤ h then h - 1 else b + 1

lemma projected_gain_upper {m : ℕ} (v h b : ℝ) (hhb : h < b) (hbv : b ≤ v)
    (cy : Fin m → Bool × ℝ) (z : Fin m → ℝ) :
    payoff v h (mixBids cy z) - payoff v b (mixBids cy z) ≤
      payoff v h (mixBids cy (favorableProjection h b z)) -
        payoff v b (mixBids cy (favorableProjection h b z)) := by
  classical
  have hup : payoff v h (mixBids cy z) ≤ payoff v h (mixBids cy (favorableProjection h b z)) := by
    by_cases hw : ∀ i, mixBids cy z i ≤ h
    · have hw' : ∀ i, mixBids cy (favorableProjection h b z) i ≤ h := by
        intro i
        have hi := hw i
        by_cases hc : (cy i).1 = true
        · simpa [mixBids, hc] using hi
        · have hz : z i ≤ h := by simpa [mixBids, hc] using hi
          simp [mixBids, hc, favorableProjection, hz]
      have hsub : (Finset.univ.filter (fun i => mixBids cy (favorableProjection h b z) i = h)) ⊆
          Finset.univ.filter (fun i => mixBids cy z i = h) := by
        intro i hi
        have he := (Finset.mem_filter.mp hi).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hc : (cy i).1 = true
        · simpa [mixBids, hc] using he
        · have hz : z i ≤ h := by simpa [mixBids, hc] using hw i
          have he' : h - 1 = h := by simpa [mixBids, hc, favorableProjection, hz] using he
          linarith
      have hc : ((Finset.univ.filter (fun i => mixBids cy (favorableProjection h b z) i = h)).card : ℝ) ≤
          ((Finset.univ.filter (fun i => mixBids cy z i = h)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      simp only [payoff, if_pos hw, if_pos hw']
      exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    · rw [payoff, if_neg hw]
      exact payoff_nonnegative v h (hhb.le.trans hbv) _
  have hlo : payoff v b (mixBids cy (favorableProjection h b z)) ≤ payoff v b (mixBids cy z) := by
    by_cases hw : ∀ i, mixBids cy (favorableProjection h b z) i ≤ b
    · have hw' : ∀ i, mixBids cy z i ≤ b := by
        intro i
        have hi := hw i
        by_cases hc : (cy i).1 = true
        · simpa [mixBids, hc] using hi
        · by_cases hz : z i ≤ h
          · simp only [mixBids, if_neg hc]
            exact hz.trans hhb.le
          · have hi' : b + 1 ≤ b := by simpa [mixBids, hc, favorableProjection, hz] using hi
            linarith
      have heq : (Finset.univ.filter (fun i => mixBids cy (favorableProjection h b z) i = b)) =
          Finset.univ.filter (fun i => mixBids cy z i = b) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hc : (cy i).1 = true
        · simp [mixBids, hc]
        · by_cases hz : z i ≤ h
          · simp only [mixBids, if_neg hc, favorableProjection, if_pos hz]
            constructor <;> intro he <;> linarith
          · have hi := hw i
            simp only [mixBids, favorableProjection, if_neg hc, if_neg hz] at hi
            linarith
      simp only [payoff, if_pos hw, if_pos hw', heq]
      exact le_rfl
    · rw [payoff, if_neg hw]
      exact payoff_nonnegative v b hbv _
  exact sub_le_sub hup hlo

end RobustFPA.VarBid

namespace RobustFPA.VarBid

lemma heterogeneous_payoff (m : ℕ) (μ : Fin m → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (v b : ℝ) (hμ : ∀ i, μ i {b} = 0) :
    expUtil v b (Measure.pi μ) = (∏ i, (μ i (Set.Iio b)).toReal) * (v-b) := by
  classical
  let S : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Set.Iio b)
  have hs : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Iio)
  have hn : ∀ᵐ o ∂Measure.pi μ, ∀ i, o i ≠ b := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simpa only [not_not, Set.preimage, Set.mem_singleton_iff, Function.eval] using
      (Measure.pi_eval_preimage_null μ (i := i) (hμ i))
  have he : (fun o => payoff v b o) =ᵐ[Measure.pi μ] S.indicator (fun _ => v-b) := by
    filter_upwards [hn] with o ho
    by_cases hw : ∀ i, o i ≤ b
    · have hm : o ∈ S := by
        simpa [S, Set.mem_pi] using (fun i => lt_of_le_of_ne (hw i) (ho i))
      have hf : (Finset.univ.filter (fun i => o i = b)) = ∅ := by
        ext i
        simp [ho i]
      simp [payoff, hw, hf, Set.indicator_of_mem hm]
    · have hm : o ∉ S := by
        intro h
        have hh : ∀ i, o i < b := by simpa [S, Set.mem_pi] using h
        exact hw (fun i => (hh i).le)
      simp [payoff, hw, Set.indicator_of_notMem hm]
  unfold expUtil
  rw [integral_congr_ae he, integral_indicator_const _ hs]
  simp only [Measure.real, S, Measure.pi_pi, ENNReal.toReal_prod, smul_eq_mul]

lemma fixed_product (m : ℕ) (τ : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (z : Fin m → ℝ) :
    (constrainedLaw m τ G).map (fun cy => mixBids cy z) = Measure.pi (fun i =>
      Real.toNNReal τ • G + Real.toNNReal (1-τ) • Measure.dirac (z i)) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  unfold constrainedLaw mixBids
  have hm (i : Fin m) : Measurable (fun p : Bool × ℝ => if p.1 then p.2 else z i) :=
    Measurable.ite (by measurability) measurable_snd measurable_const
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [component_law]

lemma fixed_utility (m : ℕ) (τ L v b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) (z : Fin m → ℝ) (hzb : ∀ i, z i ≠ b) :
    (∫ cy, payoff v b (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) =
      (∏ i, (τ * ((b-L)/(v-L)) + if z i < b then 1-τ else 0)) * (v-b) := by
  letI := uniform_probability L v hLv
  have hm : Measurable (fun cy : Fin m → Bool × ℝ => mixBids cy z) := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  have he : (∫ cy, payoff v b (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) =
      expUtil v b ((constrainedLaw m τ (uniformG L v)).map (fun cy => mixBids cy z)) := by
    unfold expUtil
    exact (integral_map_of_stronglyMeasurable hm (payoff_measurable m v b).stronglyMeasurable).symm
  rw [he, fixed_product, heterogeneous_payoff _ _ _ _ (fun i => common_no_tie τ L v b (z i) (hzb i))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, uniform_Iio L v b hLv hLb hbv]
  have hratio : 0 ≤ (b-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLb) (sub_pos.mpr hLv).le
  simp [ENNReal.toReal_ofReal hratio, Real.toNNReal_of_nonneg hτ0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hτ1), Measure.dirac_apply']
  by_cases hz : z i < b <;> simp [Set.indicator, hz]

end RobustFPA.VarBid

namespace RobustFPA.VarBid

lemma fixed_integrable (m : ℕ) (τ L v b : ℝ) (z : Fin m → ℝ) :
    Integrable (fun cy => payoff v b (mixBids cy z)) (constrainedLaw m τ (uniformG L v)) := by
  letI : IsFiniteMeasure (bern τ) := by unfold bern; infer_instance
  letI : IsFiniteMeasure (constrainedLaw m τ (uniformG L v)) := by
    unfold constrainedLaw; infer_instance
  have hm : Measurable (fun cy : Fin m → Bool × ℝ => mixBids cy z) := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  apply Integrable.mono' (integrable_const |v-b|)
    ((payoff_measurable m v b).comp hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun cy => payoff_bound m v b (mixBids cy z))

lemma fixed_downward_gain (m : ℕ) (τ L v h b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hLv : L < v) (hLh : L ≤ h) (hhb : h < b) (hbv : b ≤ v) (z : Fin m → ℝ) :
    (∫ cy, payoff v h (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) -
      (∫ cy, payoff v b (mixBids cy z) ∂constrainedLaw m τ (uniformG L v)) ≤
        max ((v-h) * (1-τ+τ*((h-L)/(v-L))) ^ m -
          (v-b) * (1-τ+τ*((b-L)/(v-L))) ^ m) 0 := by
  classical
  let z' := favorableProjection h b z
  let low : Fin m → Bool := fun i => decide (z i ≤ h)
  have hhne : ∀ i, z' i ≠ h := by
    intro i
    dsimp [z', favorableProjection]
    split_ifs <;> linarith
  have hbne : ∀ i, z' i ≠ b := by
    intro i
    dsimp [z', favorableProjection]
    split_ifs <;> linarith
  have hhif (i : Fin m) : (if z' i < h then 1-τ else 0) =
      (if low i then 1-τ else 0) := by
    by_cases hi : z i ≤ h
    · simp [z', favorableProjection, hi, low, show h-1 < h by linarith]
    · simp [z', favorableProjection, hi, low, show ¬ b+1 < h by linarith]
  have hbif (i : Fin m) : (if z' i < b then 1-τ else 0) =
      (if low i then 1-τ else 0) := by
    by_cases hi : z i ≤ h
    · simp [z', favorableProjection, hi, low, show h-1 < b by linarith]
    · simp [z', favorableProjection, hi, low, show ¬ b+1 < b by linarith]
  have hmono := integral_mono
    ((fixed_integrable m τ L v h z).sub (fixed_integrable m τ L v b z))
    ((fixed_integrable m τ L v h z').sub (fixed_integrable m τ L v b z'))
    (fun cy => projected_gain_upper v h b hhb hbv cy z)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (fixed_integrable m τ L v h z) (fixed_integrable m τ L v b z),
    integral_sub (fixed_integrable m τ L v h z') (fixed_integrable m τ L v b z')] at hmono
  apply hmono.trans
  rw [fixed_utility m τ L v h hτ0 hτ1.le hLv hLh (hhb.le.trans hbv) z' hhne,
    fixed_utility m τ L v b hτ0 hτ1.le hLv (hLh.trans hhb.le) hbv z' hbne]
  simp_rw [hhif, hbif]
  have hp : 0 ≤ (h-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLh) (sub_pos.mpr hLv).le
  have hpq : (h-L)/(v-L) ≤ (b-L)/(v-L) :=
    (div_le_div_iff_of_pos_right (sub_pos.mpr hLv)).mpr (by linarith)
  have hb := binary_product_gain_bound low τ ((h-L)/(v-L)) ((b-L)/(v-L)) (v-h) (v-b)
    hτ0 hτ1 hp hpq (by linarith)
  simpa only [Fintype.card_fin, mul_comm] using hb

lemma arbitrary_downward_gain (n : ℕ) (τ L v h b : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hLv : L < v) (hLh : L ≤ h) (hhb : h < b) (hbv : b ≤ v)
    (H : Measure (Fin (n-1) → ℝ)) [IsProbabilityMeasure H] :
    expUtil v h (envOf n τ (uniformG L v) H) -
      expUtil v b (envOf n τ (uniformG L v) H) ≤
        max (uPlus n τ L v h - uPlus n τ L v b) 0 := by
  letI := bern_probability τ hτ0 hτ1.le
  letI := uniform_probability L v hLv
  letI : IsProbabilityMeasure (constrainedLaw (n-1) τ (uniformG L v)) := by
    unfold constrainedLaw; infer_instance
  let μ := (constrainedLaw (n-1) τ (uniformG L v)).prod H
  have hih := mixed_integrable v h (fun p => mixBids p.1 p.2) measurable_mix μ
  have hib := mixed_integrable v b (fun p => mixBids p.1 p.2) measurable_mix μ
  have hfub := integral_prod_symm _ (hih.sub hib)
  simp only [Pi.sub_apply] at hfub
  rw [environment_integral, environment_integral, ← integral_sub hih hib, hfub]
  have hh := integral_mono (hih.sub hib).integral_prod_right
    (integrable_const (max (uPlus n τ L v h - uPlus n τ L v b) 0)) (fun z => by
      change (∫ cy, payoff v h (mixBids cy z) - payoff v b (mixBids cy z)
        ∂constrainedLaw (n-1) τ (uniformG L v)) ≤ _
      rw [integral_sub (fixed_integrable (n-1) τ L v h z) (fixed_integrable (n-1) τ L v b z)]
      simpa only [uPlus] using fixed_downward_gain (n-1) τ L v h b hτ0 hτ1 hLv hLh hhb hbv z)
  simp only [Pi.sub_apply, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  convert hh using 1 <;> rfl

end RobustFPA.VarBid

namespace RobustFPA.VarBid

lemma admissible_downward_gain (n : ℕ) (τ L v h b : ℝ) (hτ1 : τ < 1)
    (hLv : L < v) (hLh : L ≤ h) (hhb : h ≤ b) (hbv : b ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    expUtil v h B - expUtil v b B ≤ tooHigh n τ L v b := by
  have hLb : L ≤ b := hLh.trans hhb
  have hc : Continuous (uPlus n τ L v) := by unfold uPlus; fun_prop
  have hbounded : BddAbove (uPlus n τ L v '' Set.Icc L b) :=
    (isCompact_Icc.image hc).bddAbove
  have hself : uPlus n τ L v b ≤ sSup (uPlus n τ L v '' Set.Icc L b) :=
    le_csSup hbounded ⟨b, ⟨hLb, le_rfl⟩, rfl⟩
  have hzero : 0 ≤ tooHigh n τ L v b := sub_nonneg.mpr hself
  by_cases he : h = b
  · simpa only [he, sub_self] using hzero
  have hstrict : h < b := lt_of_le_of_ne hhb he
  have hbound : uPlus n τ L v h - uPlus n τ L v b ≤ tooHigh n τ L v b :=
    sub_le_sub_right (le_csSup hbounded ⟨h, ⟨hLh, hhb⟩, rfl⟩) _
  rcases hB with ⟨_, _, hτ0, _, _, _, H, hH, _, rfl⟩
  letI := hH
  exact (arbitrary_downward_gain n τ L v h b hτ0 hτ1 hLv hLh hstrict hbv H).trans
    (max_le hbound hzero)

end RobustFPA.VarBid

open RobustFPA.VarBid



namespace RobustFPA.VarBid

lemma admissible_lower_support (n : ℕ) (τ L : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L G) :
    ∀ᵐ o ∂B, ∀ i, L ≤ o i := by
  rcases hB with ⟨_, _, hτ0, hτ1, hG, hGL, H, hH, hHL, rfl⟩
  letI := hG
  letI := hH
  letI := bern_probability τ hτ0 hτ1
  have hga : ∀ᵐ y ∂G, L ≤ y := by
    apply ae_iff.mpr
    simpa [Set.Iio, not_le] using hGL
  have hp : ∀ᵐ y : Bool × ℝ ∂(bern τ).prod G, L ≤ y.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Filter.Eventually.of_forall (fun _ => hga)
  have hcy : ∀ᵐ cy ∂constrainedLaw (n-1) τ G, ∀ i, L ≤ (cy i).2 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n-1) => (bern τ).prod G)
      (i := i)).eventually hp
  have hz : ∀ᵐ z ∂H, ∀ i, L ≤ z i :=
    (mem_ae_iff_prob_eq_one (by measurability)).mpr hHL
  have hS : MeasurableSet {o : Fin (n-1) → ℝ | ∀ i, L ≤ o i} := by measurability
  unfold envOf
  apply (ae_map_iff measurable_mix.aemeasurable hS).mpr
  apply (Measure.ae_prod_iff_ae_ae (hS.preimage measurable_mix)).mpr
  filter_upwards [hcy] with cy hcy
  filter_upwards [hz] with z hz
  intro i
  simp only [mixBids]
  split_ifs
  · exact hcy i
  · exact hz i

lemma utility_below_floor (n : ℕ) (hn : 2 ≤ n) (τ L v h : ℝ) (hhL : h < L)
    (G : Measure ℝ) [IsFiniteMeasure G]
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L G) :
    expUtil v h B = 0 := by
  have hz : (fun o => payoff v h o) =ᵐ[B] fun _ => 0 := by
    filter_upwards [admissible_lower_support n τ L G B hB] with o ho
    have hnwin : ¬ ∀ i, o i ≤ h := by
      intro hw
      let i : Fin (n-1) := ⟨0, by omega⟩
      exact (not_le_of_gt hhL) ((ho i).trans (hw i))
    simp [payoff, hnwin]
  unfold expUtil
  rw [integral_congr_ae hz, integral_zero]

lemma utility_nonnegative (m : ℕ) (v b : ℝ) (hbv : b ≤ v)
    (B : Measure (Fin m → ℝ)) : 0 ≤ expUtil v b B := by
  apply integral_nonneg
  intro o
  unfold payoff
  split_ifs
  · apply div_nonneg (sub_nonneg.mpr hbv)
    positivity
  · exact le_rfl

lemma utility_above_value (m : ℕ) (v h : ℝ) (hvh : v ≤ h)
    (B : Measure (Fin m → ℝ)) : expUtil v h B ≤ 0 := by
  apply integral_nonpos
  intro o
  unfold payoff
  split_ifs
  · apply div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvh)
    positivity
  · exact le_rfl

lemma uPlus_ray_bound (n : ℕ) (τ L v h : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hLv : L < v) (hLh : L ≤ h) : uPlus n τ L v h ≤ v-L := by
  have hp0 : 0 ≤ (h-L)/(v-L) := div_nonneg (sub_nonneg.mpr hLh) (sub_pos.mpr hLv).le
  have ha0 : 0 ≤ 1-τ+τ*((h-L)/(v-L)) := by positivity
  unfold uPlus
  by_cases hhv : h ≤ v
  · have hp1 : (h-L)/(v-L) ≤ 1 := (div_le_one (sub_pos.mpr hLv)).mpr (by linarith)
    have ha1 : 1-τ+τ*((h-L)/(v-L)) ≤ 1 := by nlinarith
    have hpow : (1-τ+τ*((h-L)/(v-L)))^(n-1) ≤ 1 := pow_le_one₀ ha0 ha1
    calc
      (v-h) * (1-τ+τ*((h-L)/(v-L)))^(n-1) ≤ (v-h)*1 :=
        mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hhv)
      _ ≤ v-L := by linarith
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg ha0 _)).trans
      (sub_pos.mpr hLv).le

lemma all_deviations_upper (n : ℕ) (hn : 2 ≤ n) (τ L v b h : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v)
    (B : Measure (Fin (n-1) → ℝ)) (hB : B ∈ varBidSet n τ L (uniformG L v)) :
    expUtil v h B - expUtil v b B ≤ max (tooHigh n τ L v b) (tooLow n τ L v b) := by
  have hnonneg : 0 ≤ tooHigh n τ L v b := by
    have hc : Continuous (uPlus n τ L v) := by unfold uPlus; fun_prop
    exact sub_nonneg.mpr (le_csSup (isCompact_Icc.image hc).bddAbove ⟨b, ⟨hLb, le_rfl⟩, rfl⟩)
  have hz : 0 ≤ max (tooHigh n τ L v b) (tooLow n τ L v b) :=
    hnonneg.trans (le_max_left _ _)
  by_cases hLh : L ≤ h
  · by_cases hhv : h ≤ v
    · by_cases hhb : h ≤ b
      · exact (admissible_downward_gain n τ L v h b hτ1 hLv hLh hhb hbv B hB).trans
          (le_max_left _ _)
      · have hbounded : BddAbove (uPlus n τ L v '' Set.Ioi b) := by
          refine ⟨v-L, ?_⟩
          rintro _ ⟨y, hy, rfl⟩
          exact uPlus_ray_bound n τ L v y hτ0.le hτ1.le hLv (hLb.trans hy.le)
        have hu : uPlus n τ L v h - uMinus n τ L v b ≤ tooLow n τ L v b :=
          sub_le_sub_right (le_csSup hbounded ⟨h, lt_of_not_ge hhb, rfl⟩) _
        exact (deviation_upper n τ L v b h hLv hLb hbv hLh hhv B hB).trans
          (hu.trans (le_max_right _ _))
    · exact (sub_nonpos.mpr ((utility_above_value (n-1) v h (le_of_not_ge hhv) B).trans
        (utility_nonnegative (n-1) v b hbv B))).trans hz
  · rw [utility_below_floor n hn τ L v h (lt_of_not_ge hLh) (uniformG L v) B hB]
    exact (sub_nonpos.mpr (utility_nonnegative (n-1) v b hbv B)).trans hz

lemma maximal_loss_upper (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) (hLb : L ≤ b) (hbv : b ≤ v) :
    maxLoss v b (varBidSet n τ L (uniformG L v)) ≤ max (tooHigh n τ L v b) (tooLow n τ L v b) := by
  unfold maxLoss
  apply csSup_le
  · exact ⟨loss v b (commonBidEnv n τ (uniformG L v) L),
      commonBidEnv n τ (uniformG L v) L,
      common_admissible n hn τ L v hτ0 hτ1 hL hLv L le_rfl, rfl⟩
  · rintro _ ⟨B, hB, rfl⟩
    unfold loss
    apply sub_le_iff_le_add.mpr
    apply csSup_le
    · exact ⟨expUtil v 0 B, 0, by simp, rfl⟩
    · rintro _ ⟨h, _, rfl⟩
      exact sub_le_iff_le_add.mp (all_deviations_upper n hn τ L v b h hτ0 hτ1 hLv hLb hbv B hB)

end RobustFPA.VarBid

open RobustFPA.VarBid in
theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hL : 0 ≤ L) (hLv : L < v) (b : ℝ) (hLb : L ≤ b) (hbv : b ≤ v) :
    maxLoss v b (varBidSet n τ L (uniformG L v)) = max (tooHigh n τ L v b) (tooLow n τ L v b) := by
  exact le_antisymm (maximal_loss_upper n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)
    (analytic_max_lower_bound n hn τ L v b hτ0 hτ1 hL hLv hLb hbv)
