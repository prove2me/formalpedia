-- Prove2me | solution 1 for PhysReaudit.sprt_validity
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T09:49:46.076977+00:00
-- url     : https://prove2.me/submissions/446b8038-2731-42b7-96d3-7b13f0200ead

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_PhysReaudit_mu
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_run
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_fullTraversalRule
import Definitions.Def_PhysReaudit_sprtS
import Definitions.Def_PhysReaudit_sprtRule
import Theorems.Thm_PhysReaudit_multiplier_ge_t
import Theorems.Thm_PhysReaudit_reciprocal_supermartingale

open MeasureTheory

namespace PRSprtValidity

open PhysReaudit

/-- Ville's inequality for a nonnegative supermartingale started at `1`. -/
theorem ville {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} (hf : Supermartingale f 𝒢 μ)
    (hnn : ∀ n ω, 0 ≤ f n ω) (h0 : ∀ ω, f 0 ω = 1) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ k, c ≤ f k ω} ≤ ENNReal.ofReal (1 / c) := by
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    ((hf.stronglyAdapted k).mono (𝒢.le k)).measurable
  have key : ∀ n, μ {ω | ∃ k ≤ n, c ≤ f k ω} ≤ ENNReal.ofReal (1 / c) := by
    intro n
    set A := {ω | ∃ k ≤ n, c ≤ f k ω} with hA
    have hAm : MeasurableSet A := by
      have : A = ⋃ k, ⋃ (_ : k ≤ n), {ω | c ≤ f k ω} := by ext ω; simp [hA]
      rw [this]
      exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
        measurableSet_le measurable_const (hmeas k)
    set π : Ω → ℕ∞ := fun ω => ((hittingBtwn f {y : ℝ | c ≤ y} 0 n ω : ℕ) : ℕ∞) with hπdef
    have hπ : IsStoppingTime 𝒢 π :=
      hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hbdd : ∀ ω, π ω ≤ n := fun ω => by
      simp only [hπdef]
      exact_mod_cast (hittingBtwn_le (u := f) (s := {y : ℝ | c ≤ y}) (n := 0) ω)
    have hmono := hf.neg.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hπ
      (fun ω => by simp only [Nat.cast_zero]; exact bot_le) hbdd
    have hsv : ∀ ω, stoppedValue (-f) π ω = - stoppedValue f π ω := fun ω => rfl
    have hint : Integrable (stoppedValue f π) μ := hf.neg.integrable_stoppedValue hπ hbdd |>.neg.congr
      (Filter.Eventually.of_forall fun ω => by simp [hsv])
    have h1 : ∫ ω, stoppedValue f π ω ∂μ ≤ 1 := by
      rw [stoppedValue_const] at hmono
      have e0 : (-f) 0 = fun ω => -1 := by
        funext ω; simp [h0]
      rw [e0] at hmono
      have : ∫ ω, stoppedValue (-f) π ω ∂μ = - ∫ ω, stoppedValue f π ω ∂μ := by
        simp_rw [hsv]; exact integral_neg _
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
      linarith
    have h2 : c * μ.real A ≤ ∫ ω in A, stoppedValue f π ω ∂μ := by
      refine setIntegral_ge_of_const_le_real hAm (measure_ne_top _ _) ?_ hint.integrableOn
      intro ω hω
      obtain ⟨k, hk, hck⟩ := hω
      exact stoppedValue_hittingBtwn_mem (u := f) (s := {y : ℝ | c ≤ y}) ⟨k, ⟨Nat.zero_le _, hk⟩, hck⟩
    have h3 : ∫ ω in A, stoppedValue f π ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => hnn _ _)
    have h4 : μ.real A ≤ 1 / c := by
      rw [le_div_iff₀ hc]; linarith
    rw [← ofReal_measureReal (measure_ne_top μ A)]
    exact ENNReal.ofReal_le_ofReal h4
  have hU : {ω | ∃ k, c ≤ f k ω} = ⋃ n, {ω | ∃ k ≤ n, c ≤ f k ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k, le_rfl, hk⟩, fun ⟨_, k, _, hk⟩ => ⟨k, hk⟩⟩
  rw [hU, Monotone.measure_iUnion]
  · exact iSup_le key
  · intro a b hab ω ⟨k, hk, h⟩; exact ⟨k, hk.trans hab, h⟩

theorem bern_prob {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : IsProbabilityMeasure (bern r) := by
  constructor
  simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]; simp

theorem sprtS_meas (q₀ t : ℝ) (n : ℕ) :
    Measurable[pastFiltration n] (fun y : ℕ → Bool => sprtS q₀ t y n) := by
  unfold sprtS
  refine Finset.measurable_sum _ fun i hi => ?_
  have hy : Measurable[pastFiltration n] (fun y : ℕ → Bool => y i) := by
    have : MeasurableSpace.comap (fun y : ℕ → Bool => y i) inferInstance ≤ pastFiltration n :=
      le_iSup₂ (f := fun j (_ : j ∈ Finset.range n) =>
        MeasurableSpace.comap (fun y : ℕ → Bool => y j) inferInstance) i hi
    exact (comap_measurable _).mono this le_rfl
  exact (measurable_of_countable (sprtIncr q₀ t)).comp hy

theorem sprtS_abs_le (q₀ t : ℝ) (y : ℕ → Bool) (n : ℕ) :
    |sprtS q₀ t y n| ≤ n * (|zMinus q₀ t| + |zPlus q₀ t|) := by
  unfold sprtS
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ Finset.range n, |sprtIncr q₀ t (y i)| ≤ |zMinus q₀ t| + |zPlus q₀ t| := by
    intro i _
    unfold sprtIncr; split_ifs
    · linarith [abs_nonneg (zPlus q₀ t)]
    · linarith [abs_nonneg (zMinus q₀ t)]
  have h := Finset.sum_le_sum this
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact h

theorem exp_sprtS_integrable (q₀ t : ℝ) (σ : ℝ) (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (n : ℕ) : Integrable (fun y => Real.exp (σ * sprtS q₀ t y n)) μ := by
  refine Integrable.of_bound ?_ (Real.exp (|σ| * (n * (|zMinus q₀ t| + |zPlus q₀ t|)))) ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul
      ((sprtS_meas q₀ t n).mono ((pastFiltration).le n) le_rfl))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc σ * sprtS q₀ t y n ≤ |σ * sprtS q₀ t y n| := le_abs_self _
      _ = |σ| * |sprtS q₀ t y n| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (sprtS_abs_le q₀ t y n) (abs_nonneg _)

theorem supermart {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) {q : ℝ}
    (hq : q ∈ Set.Icc t 1) :
    Supermartingale (fun n y => Real.exp (sprtS q₀ t y n)) pastFiltration
      (Measure.infinitePi fun _ : ℕ => bern q) := by
  have := bern_prob (r := q) (by linarith [hq.1, h0, h1]) hq.2
  set μ := Measure.infinitePi fun _ : ℕ => bern q
  have hI : ∀ n, Integrable (fun y => Real.exp (sprtS q₀ t y n)) μ := fun n => by
    simpa using exp_sprtS_integrable q₀ t 1 μ n
  refine supermartingale_nat (fun n => ?_) hI (fun i => ?_)
  · exact (Real.measurable_exp.comp (sprtS_meas q₀ t n)).stronglyMeasurable
  · obtain ⟨hce, hc1⟩ := multiplier_ge_t h0 h1 h2 hq i
    set g : (ℕ → Bool) → ℝ := fun y => Real.exp (sprtS q₀ t y (i + 1) - sprtS q₀ t y i)
    have hsplit : (fun y => Real.exp (sprtS q₀ t y (i + 1)))
        = (fun y => Real.exp (sprtS q₀ t y i)) * g := by
      funext y; simp only [Pi.mul_apply, g, ← Real.exp_add]; ring_nf
    have hgI : Integrable g μ := by
      have : g = fun y => Real.exp (sprtIncr q₀ t (y i)) := by
        funext y; simp [g, sprtS, Finset.sum_range_succ]
      rw [this]
      refine Integrable.of_bound ?_ (Real.exp (|zMinus q₀ t| + |zPlus q₀ t|)) ?_
      · exact (Real.measurable_exp.comp ((measurable_of_countable (sprtIncr q₀ t)).comp
          (measurable_pi_apply i : Measurable fun y : ℕ → Bool => y i))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun y => ?_
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.2
        unfold sprtIncr; split_ifs
        · linarith [le_abs_self (zMinus q₀ t), abs_nonneg (zPlus q₀ t)]
        · linarith [le_abs_self (zPlus q₀ t), abs_nonneg (zMinus q₀ t)]
    rw [hsplit]
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := pastFiltration i) (μ := μ)
      (f := fun y => Real.exp (sprtS q₀ t y i)) (g := g)
      (Real.measurable_exp.comp (sprtS_meas q₀ t i)).stronglyMeasurable (by rw [← hsplit]; exact hI _)
      hgI
    filter_upwards [hpull, hce] with y hy1 hy2
    rw [hy1, Pi.mul_apply, hy2]
    exact mul_le_of_le_one_right (Real.exp_pos _).le hc1

/-- The SPRT statistic of the recorded target outcomes equals `S` at the number of target entries used. -/
theorem targets_sum {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W)
    (q₀ t : ℝ) (n : ℕ) :
    ((targets (run R d ω n).hist).map (sprtIncr q₀ t)).sum
      = sprtS q₀ t ω.2.2 (run R d ω n).tgtUsed := by
  induction n with
  | zero => simp [run, Cfg.init, targets, sprtS]
  | succ n ih =>
    simp only [run]
    generalize R.decide ω.1 (run R d ω n).hist = act
    generalize hc : run R d ω n = c at ih
    unfold step
    rcases c with ⟨hist, pos, nu, tu, hl⟩
    rcases hl with _ | b
    · cases act with
      | accept => simpa using ih
      | stop => simpa using ih
      | setup => simpa [targets] using ih
      | attempt =>
        rcases pos with _ | i
        · simpa [targets] using ih
        · simp only
          split_ifs
          all_goals first
            | simpa [targets] using ih
            | (have e : ∀ L : List Obs, targets (Obs.target (ω.2.2 tu) :: L) = ω.2.2 tu :: targets L :=
                 fun L => rfl
               simp only [e, List.map_cons, List.sum_cons] at ih ⊢
               rw [ih]; simp only [sprtS, Finset.sum_range_succ]; ring)
    · simpa using ih

/-- For the SPRT rule, a halted state with outcome `b` was reached because `sprtStop` returned `b`. -/
theorem sprt_halted {W : Type} [MeasurableSpace W] (q₀ t δ : ℝ) (d : ℕ) (ω : Omega W) (n : ℕ)
    (b : Bool) (h : (run (sprtRule W q₀ t δ) d ω n).halted = some b) :
    sprtStop q₀ t δ (targets (run (sprtRule W q₀ t δ) d ω n).hist) = some b := by
  induction n with
  | zero => simp [run, Cfg.init] at h
  | succ n ih =>
    simp only [run] at h ⊢
    generalize hc : run (sprtRule W q₀ t δ) d ω n = c at ih h
    rcases c with ⟨hist, pos, nu, tu, hl⟩
    rcases hl with _ | b'
    · simp only [sprtRule, fullTraversalRule] at h ⊢
      generalize hs : sprtStop q₀ t δ (targets hist) = s at h ⊢
      rcases s with _ | _ | _
      · simp only at h ⊢
        split_ifs at h ⊢ with he
        · unfold step at h; simp only at h
          rcases pos with _ | i
          · simp at h
          · simp only at h; split_ifs at h <;> simp at h
        · simp [step] at h
      · simp [step] at h ⊢; subst h; exact hs
      · simp [step] at h ⊢; subst h; exact hs
    · simp only [step] at h ⊢; exact ih h

theorem accept_imp {W : Type} [MeasurableSpace W] (q₀ t δ : ℝ) (hδ : 0 < δ) (d : ℕ) (ω : Omega W)
    (h : accepts (sprtRule W q₀ t δ) d ω) :
    ∃ k, 1 / δ ≤ Real.exp (sprtS q₀ t ω.2.2 k) := by
  obtain ⟨n, hn⟩ := h
  have hs := sprt_halted q₀ t δ d ω n true hn
  unfold sprtStop at hs
  rw [targets_sum] at hs
  refine ⟨(run (sprtRule W q₀ t δ) d ω n).tgtUsed, ?_⟩
  split_ifs at hs with ha hb hc
  all_goals first
    | (simp at hs; done)
    | (rw [← Real.exp_log (show 0 < 1 / δ by positivity)]
       exact Real.exp_le_exp.2 hb)

theorem lower_imp {W : Type} [MeasurableSpace W] (q₀ t δ : ℝ) (hδ : 0 < δ) (d : ℕ) (ω : Omega W)
    (h : stops (sprtRule W q₀ t δ) d ω ∧ ¬ accepts (sprtRule W q₀ t δ) d ω) :
    ∃ k, 1 / δ ≤ Real.exp (-sprtS q₀ t ω.2.2 k) := by
  obtain ⟨⟨n, hn⟩, hna⟩ := h
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hn
  cases b with
  | true => exact absurd ⟨n, hb⟩ hna
  | false =>
    have hs := sprt_halted q₀ t δ d ω n false hb
    unfold sprtStop at hs
    rw [targets_sum] at hs
    refine ⟨(run (sprtRule W q₀ t δ) d ω n).tgtUsed, ?_⟩
    split_ifs at hs with ha hb hc
    all_goals first
      | (simp at hs; done)
      | (rw [← Real.exp_log (show 0 < 1 / δ by positivity)]
         exact Real.exp_le_exp.2 (by linarith))

theorem marginal {W : Type} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν]
    {a q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {F : Set (ℕ → Bool)}
    (hF : MeasurableSet F) :
    lawQ ν a q ((fun ω : Omega W => ω.2.2) ⁻¹' F) = Measure.infinitePi (fun _ : ℕ => bern q) F := by
  haveI := bern_prob ha0 ha1
  haveI := bern_prob hq0 hq1
  have : (fun ω : Omega W => ω.2.2) ⁻¹' F = Set.univ ×ˢ (Set.univ ×ˢ F) := by
    ext ω; simp
  rw [this, lawQ, Measure.prod_prod, Measure.prod_prod]
  simp

end PRSprtValidity

open PhysReaudit in
theorem solution {W : Type} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν]
    {q₀ t δ a : ℝ} {d : ℕ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∀ q ∈ Set.Icc t 1, (∀ n y, 0 ≤ Real.exp (sprtS q₀ t y n)) ∧
      Supermartingale (fun n y => Real.exp (sprtS q₀ t y n)) pastFiltration
        (Measure.infinitePi fun _ : ℕ => bern q)) ∧
    (∀ q ∈ Set.Icc t 1,
      lawQ ν a q {ω | accepts (sprtRule W q₀ t δ) d ω} ≤ ENNReal.ofReal δ) ∧
    (∀ q ∈ Set.Icc 0 q₀,
      lawQ ν a q {ω | stops (sprtRule W q₀ t δ) d ω ∧ ¬ accepts (sprtRule W q₀ t δ) d ω}
        ≤ ENNReal.ofReal δ) := by
  refine ⟨fun q hq => ⟨fun n y => (Real.exp_pos _).le, PRSprtValidity.supermart h0 h1 h2 hq⟩,
    fun q hq => ?_, fun q hq => ?_⟩
  · have hq0 : 0 ≤ q := by linarith [hq.1]
    have := PRSprtValidity.bern_prob hq0 hq.2
    set F := {y : ℕ → Bool | ∃ k, 1 / δ ≤ Real.exp (sprtS q₀ t y k)} with hF
    have hFm : MeasurableSet F := by
      have : F = ⋃ k, {y : ℕ → Bool | 1 / δ ≤ Real.exp (sprtS q₀ t y k)} := by ext; simp [hF]
      rw [this]
      exact MeasurableSet.iUnion fun k => measurableSet_le measurable_const
        (Real.measurable_exp.comp ((PRSprtValidity.sprtS_meas q₀ t k).mono
          ((pastFiltration).le k) le_rfl))
    calc lawQ ν a q {ω | accepts (sprtRule W q₀ t δ) d ω}
        ≤ lawQ ν a q ((fun ω : Omega W => ω.2.2) ⁻¹' F) :=
          measure_mono fun ω h => PRSprtValidity.accept_imp q₀ t δ hδ d ω h
      _ = Measure.infinitePi (fun _ : ℕ => bern q) F :=
          PRSprtValidity.marginal ν ha.le ha1 hq0 hq.2 hFm
      _ ≤ ENNReal.ofReal (1 / (1 / δ)) :=
          PRSprtValidity.ville (PRSprtValidity.supermart h0 h1 h2 hq)
            (fun n y => (Real.exp_pos _).le) (fun y => by simp [sprtS]) (by positivity)
      _ = ENNReal.ofReal δ := by rw [one_div_one_div]
  · have hq1 : q ≤ 1 := by linarith [hq.2]
    have := PRSprtValidity.bern_prob hq.1 hq1
    obtain ⟨-, hnn, hsm⟩ := reciprocal_supermartingale h0 h1 h2 hq
    set F := {y : ℕ → Bool | ∃ k, 1 / δ ≤ Real.exp (-sprtS q₀ t y k)} with hF
    have hFm : MeasurableSet F := by
      have : F = ⋃ k, {y : ℕ → Bool | 1 / δ ≤ Real.exp (-sprtS q₀ t y k)} := by ext; simp [hF]
      rw [this]
      exact MeasurableSet.iUnion fun k => measurableSet_le measurable_const
        (Real.measurable_exp.comp ((PRSprtValidity.sprtS_meas q₀ t k).mono
          ((pastFiltration).le k) le_rfl).neg)
    calc lawQ ν a q {ω | stops (sprtRule W q₀ t δ) d ω ∧ ¬ accepts (sprtRule W q₀ t δ) d ω}
        ≤ lawQ ν a q ((fun ω : Omega W => ω.2.2) ⁻¹' F) :=
          measure_mono fun ω h => PRSprtValidity.lower_imp q₀ t δ hδ d ω h
      _ = Measure.infinitePi (fun _ : ℕ => bern q) F :=
          PRSprtValidity.marginal ν ha.le ha1 hq.1 hq1 hFm
      _ ≤ ENNReal.ofReal (1 / (1 / δ)) :=
          PRSprtValidity.ville hsm hnn (fun y => by simp [sprtS]) (by positivity)
      _ = ENNReal.ofReal δ := by rw [one_div_one_div]
