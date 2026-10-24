-- Prove2me | solution 1 for SampleDrivenOS.Limit.lemma_6_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:14:50.911952+00:00
-- url     : https://prove2.me/submissions/a652bf9d-4de2-47ac-a4df-f91dbec37a7f

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting
import Theorems.Thm_SampleDrivenOS_Limit_lemma_6_i
import Theorems.Thm_SampleDrivenOS_Limit_lemma_6_ii
import Theorems.Thm_SampleDrivenOS_Limit_b6_product_identity
import Theorems.Thm_SampleDrivenOS_Limit_b4_binomial_identity

open MeasureTheory Filter Topology Set

namespace L6iiiAux

open SampleDrivenOS.Limit SampleDrivenOS.Structure

section generic

variable {p : ℝ} {t : ℕ → ℝ}

lemma uniq (hmono : Monotone t) {τ : ℝ} {i j : ℕ} (hi1 : t i ≤ τ) (hi2 : τ < t (i + 1))
    (hj1 : t j ≤ τ) (hj2 : τ < t (j + 1)) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := hmono (show i + 1 ≤ j by omega); linarith
  · have := hmono (show j + 1 ≤ i by omega); linarith

lemma tq_eq (hmono : Monotone t) {τ : ℝ} {i : ℕ} (hi1 : t i ≤ τ) (hi2 : τ < t (i + 1)) (ℓ : ℕ) :
    thresholdQ t τ ℓ = if ℓ ≤ i then thresholdProd t i / τ ^ (i + 1) else 0 := by
  have hex : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1) := ⟨i, hi1, hi2⟩
  unfold thresholdQ
  rw [dif_pos hex]
  have hf : Nat.find hex = i := uniq hmono (Nat.find_spec hex).1 (Nat.find_spec hex).2 hi1 hi2
  rw [hf]

lemma tq_none {τ : ℝ} (h : ¬ ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)) (ℓ : ℕ) :
    thresholdQ t τ ℓ = 0 := by
  unfold thresholdQ
  rw [dif_neg h]

lemma T_pos (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (i : ℕ) : 0 < thresholdProd t i := by
  unfold thresholdProd
  apply Finset.prod_pos
  intro j _
  exact lt_of_lt_of_le hp0 (hge j)

lemma T_le (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (i : ℕ) :
    thresholdProd t i ≤ t i ^ i := by
  unfold thresholdProd
  calc ∏ j ∈ Finset.Icc 1 i, t j ≤ ∏ _j ∈ Finset.Icc 1 i, t i :=
        Finset.prod_le_prod (fun j _ => le_trans hp0.le (hge j))
          (fun j hj => hmono (Finset.mem_Icc.1 hj).2)
    _ = t i ^ i := by simp [Finset.prod_const]

lemma T_succ (i : ℕ) : thresholdProd t (i + 1) = thresholdProd t i * t (i + 1) := by
  unfold thresholdProd
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma no_zero (ht0 : t 0 = p) (ht1 : t 1 = p) {τ : ℝ} (h1 : t 0 ≤ τ) (h2 : τ < t (0 + 1)) : False := by
  simp only [zero_add] at h2
  rw [ht0] at h1; rw [ht1] at h2; linarith

lemma tq_nonneg (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (τ : ℝ) (ℓ : ℕ) :
    0 ≤ thresholdQ t τ ℓ := by
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    rw [tq_eq hmono hi1 hi2]
    split_ifs
    · have := T_pos hp0 hge i
      have : 0 < τ := lt_of_lt_of_le hp0 (le_trans (hge i) hi1)
      positivity
    · exact le_rfl
  · rw [tq_none h]

lemma tq_le (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (τ : ℝ) (ℓ : ℕ) : thresholdQ t τ ℓ ≤ 1 / p := by
  have hp' : 0 ≤ 1 / p := by positivity
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    rw [tq_eq hmono hi1 hi2]
    split_ifs
    · have hT := T_le hp0 hge hmono i
      have hTp := T_pos hp0 hge i
      have hti : 0 < t i := lt_of_lt_of_le hp0 (hge i)
      have hτ : 0 < τ := lt_of_lt_of_le hti hi1
      calc thresholdProd t i / τ ^ (i + 1) ≤ t i ^ i / t i ^ (i + 1) := by
            apply div_le_div₀ (by positivity) hT (by positivity)
            exact pow_le_pow_left₀ hti.le hi1 _
        _ = 1 / t i := by rw [pow_succ]; field_simp
        _ ≤ 1 / p := one_div_le_one_div_of_le hp0 (hge i)
    · exact hp'
  · rw [tq_none h]; exact hp'

lemma tq_anti (hmono : Monotone t) (τ : ℝ) {ℓ j : ℕ} (hℓj : ℓ ≤ j)
    (hnn : ∀ i, 0 ≤ thresholdProd t i / τ ^ (i + 1)) :
    thresholdQ t τ j ≤ thresholdQ t τ ℓ := by
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    rw [tq_eq hmono hi1 hi2, tq_eq hmono hi1 hi2]
    split_ifs with h1 h2 <;> first | exact le_rfl | (exfalso; omega) | exact hnn i
  · rw [tq_none h, tq_none h]

/-- `q(·, ℓ)` as a limit of finite sums of indicator pieces -/
lemma tq_measurable (hmono : Monotone t) (ℓ : ℕ) : Measurable (fun τ => thresholdQ t τ ℓ) := by
  set f : ℕ → ℝ → ℝ := fun n τ => ∑ i ∈ Finset.range n,
    (Ico (t i) (t (i + 1))).indicator
      (fun τ => if ℓ ≤ i then thresholdProd t i / τ ^ (i + 1) else 0) τ
  have hf : ∀ n, Measurable (f n) := by
    intro n
    apply Finset.measurable_sum
    intro i _
    apply Measurable.indicator _ measurableSet_Ico
    split_ifs
    · exact measurable_const.div (measurable_id.pow_const _)
    · exact measurable_const
  apply measurable_of_tendsto_metrizable hf
  rw [tendsto_pi_nhds]
  intro τ
  apply tendsto_nhds_of_eventually_eq
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    filter_upwards [eventually_gt_atTop i] with n hn
    simp only [f]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hn)]
    · rw [indicator_of_mem (show τ ∈ Ico (t i) (t (i + 1)) from ⟨hi1, hi2⟩), tq_eq hmono hi1 hi2]
    · intro j _ hji
      rw [indicator_of_notMem]
      rintro ⟨hj1, hj2⟩
      exact hji (uniq hmono hj1 hj2 hi1 hi2)
  · apply Eventually.of_forall
    intro n
    simp only [f]
    rw [tq_none h]
    apply Finset.sum_eq_zero
    intro i _
    rw [indicator_of_notMem]
    rintro ⟨hj1, hj2⟩
    exact h ⟨i, hj1, hj2⟩

lemma tq_integrableOn (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (ℓ : ℕ) (a b : ℝ) : IntegrableOn (fun τ => thresholdQ t τ ℓ) (Icc a b) := by
  apply IntegrableOn.of_bound (by simp) (tq_measurable hmono ℓ).aestronglyMeasurable (1 / p)
  apply Eventually.of_forall
  intro τ
  rw [Real.norm_eq_abs, abs_of_nonneg (tq_nonneg hp0 hge hmono τ ℓ)]
  exact tq_le hp0 hge hmono ht0 ht1 τ ℓ

/-- the integrand of `cumMass` -/
noncomputable def FF (t : ℕ → ℝ) (x : ℝ) : ENNReal := ∑' n : ℕ, ENNReal.ofReal (thresholdQ t x (n + 1))

lemma FF_eq (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) {x : ℝ} {i : ℕ}
    (hi1 : t i ≤ x) (hi2 : x < t (i + 1)) :
    FF t x = ENNReal.ofReal ((i : ℝ) * (thresholdProd t i / x ^ (i + 1))) := by
  unfold FF
  have hc : 0 ≤ thresholdProd t i / x ^ (i + 1) := by
    have := T_pos hp0 hge i
    have : 0 < x := lt_of_lt_of_le hp0 (le_trans (hge i) hi1)
    positivity
  rw [tsum_eq_sum (s := Finset.range i)]
  · rw [Finset.sum_congr rfl (g := fun _ => ENNReal.ofReal (thresholdProd t i / x ^ (i + 1)))]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast]
    · intro n hn
      rw [tq_eq hmono hi1 hi2, if_pos (by simp at hn; omega)]
  · intro n hn
    rw [tq_eq hmono hi1 hi2, if_neg (by simp at hn; omega), ENNReal.ofReal_zero]

lemma FF_none {x : ℝ} (h : ¬ ∃ i : ℕ, t i ≤ x ∧ x < t (i + 1)) : FF t x = 0 := by
  unfold FF
  simp [tq_none h]

lemma hasDeriv_Tpow (T : ℝ) (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(T / x ^ i)) ((i : ℝ) * (T / x ^ (i + 1))) x := by
  have h := ((hasDerivAt_pow i x).inv (pow_ne_zero i hx.ne')).const_mul T
  have h2 := h.neg
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  · apply Eventually.of_forall; intro y; simp [div_eq_mul_inv]

/-- the lower integral of `F` over a sub-interval of `[t_i, t_{i+1}]` -/
lemma FF_Ioc (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) {i : ℕ} (hi : 1 ≤ i)
    {a b : ℝ} (ha : t i ≤ a) (hab : a ≤ b) (hb : b ≤ t (i + 1)) :
    ∫⁻ x in Ioc a b, FF t x = ENNReal.ofReal (thresholdProd t i / a ^ i - thresholdProd t i / b ^ i) := by
  have ha0 : 0 < a := lt_of_lt_of_le hp0 (le_trans (hge i) ha)
  set T := thresholdProd t i
  have hT := T_pos hp0 hge i
  set g : ℝ → ℝ := fun x => (i : ℝ) * (T / x ^ (i + 1))
  have hgc : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const (continuousOn_pow _)
    intro x hx; exact pow_ne_zero _ (lt_of_lt_of_le ha0 hx.1).ne'
  have h1 : ∫⁻ x in Ioc a b, FF t x = ∫⁻ x in Ioc a b, ENNReal.ofReal (g x) := by
    apply setLIntegral_congr_fun_ae measurableSet_Ioc
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({b} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton)
    filter_upwards [hne] with x hx hxI
    have hxb : x < b := lt_of_le_of_ne hxI.2 (by simpa using hx)
    exact FF_eq hp0 hge hmono (le_trans ha hxI.1.le) (lt_of_lt_of_le hxb hb)
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hab]
    congr 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -(T / x ^ i))]
    · ring
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact hasDeriv_Tpow T i hi x (lt_of_lt_of_le ha0 hx.1)
    · exact (hgc.intervalIntegrable_of_Icc hab)
  · exact (hgc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro x hx
    have : 0 < x := lt_of_lt_of_le ha0 hx.1.le
    simp only [g]; positivity

lemma cumMass_eq_lint (q : ℝ → ℕ → ℝ) (hq : q = thresholdQ t) (τ : ℝ) :
    cumMass p q τ = ∫⁻ x in Icc p τ, FF t x := by
  subst hq; rfl

lemma T_div_le (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (i : ℕ) :
    thresholdProd t i / t i ^ i ≤ 1 := by
  have hti : 0 < t i := lt_of_lt_of_le hp0 (hge i)
  rw [div_le_one (by positivity)]
  exact T_le hp0 hge hmono i

lemma cumMass_ti (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht1 : t 1 = p) :
    ∀ i, 1 ≤ i → ∫⁻ x in Icc p (t i), FF t x = ENNReal.ofReal (1 - thresholdProd t i / t i ^ i) := by
  intro i hi
  induction i with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [zero_add, ht1]
      rw [Icc_self, Measure.restrict_singleton]
      have : thresholdProd t 1 = p := by unfold thresholdProd; simp [ht1]
      rw [this, pow_one, div_self hp0.ne', sub_self, ENNReal.ofReal_zero]
      simp
    · have ih' := ih h
      have hsplit : Icc p (t (n + 1)) = Icc p (t n) ∪ Ioc (t n) (t (n + 1)) :=
        (Icc_union_Ioc_eq_Icc (hge n) (hmono (Nat.le_succ n))).symm
      rw [hsplit, lintegral_union measurableSet_Ioc (Set.disjoint_left.2 fun x hx1 hx2 => absurd hx1.2 (not_le.2 hx2.1)), ih',
        FF_Ioc hp0 hge hmono h le_rfl (hmono (Nat.le_succ n)) le_rfl]
      have h1 := T_div_le hp0 hge hmono n
      have htn : 0 < t n := lt_of_lt_of_le hp0 (hge n)
      have htn1 : 0 < t (n + 1) := lt_of_lt_of_le hp0 (hge (n + 1))
      have h2 : thresholdProd t n / t (n + 1) ^ n ≤ thresholdProd t n / t n ^ n := by
        apply div_le_div_of_nonneg_left (T_pos hp0 hge n).le (by positivity)
        exact pow_le_pow_left₀ htn.le (hmono (Nat.le_succ n)) n
      rw [← ENNReal.ofReal_add (by linarith) (by linarith), T_succ, pow_succ]
      congr 1
      field_simp
      ring

lemma cumMass_in (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht1 : t 1 = p)
    {i : ℕ} (hi : 1 ≤ i) {τ : ℝ} (h1 : t i ≤ τ) (h2 : τ ≤ t (i + 1)) :
    ∫⁻ x in Icc p τ, FF t x = ENNReal.ofReal (1 - thresholdProd t i / τ ^ i) := by
  have hsplit : Icc p τ = Icc p (t i) ∪ Ioc (t i) τ := (Icc_union_Ioc_eq_Icc (hge i) h1).symm
  rw [hsplit, lintegral_union measurableSet_Ioc (Set.disjoint_left.2 fun x hx1 hx2 => absurd hx1.2 (not_le.2 hx2.1)),
    cumMass_ti hp0 hge hmono ht1 i hi, FF_Ioc hp0 hge hmono hi le_rfl h1 h2]
  have hb := T_div_le hp0 hge hmono i
  have hti : 0 < t i := lt_of_lt_of_le hp0 (hge i)
  have h3 : thresholdProd t i / τ ^ i ≤ thresholdProd t i / t i ^ i := by
    apply div_le_div_of_nonneg_left (T_pos hp0 hge i).le (by positivity)
    exact pow_le_pow_left₀ hti.le h1 i
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1; ring

lemma cumMass_le_one (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) {τ : ℝ} (hτ : p ≤ τ) : ∫⁻ x in Icc p τ, FF t x ≤ 1 := by
  by_cases hex : ∃ n, τ < t n
  · -- τ lies in some [t_i, t_{i+1})
    classical
    have hn := Nat.find_spec hex
    set n := Nat.find hex
    have hn2 : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n
      · rw [ht0] at hn; linarith
      · rw [ht1] at hn; linarith
    obtain ⟨i, hi⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    have hti : t i ≤ τ := by
      have := Nat.find_min hex (show i < n by omega)
      push Not at this; exact this
    rw [cumMass_in hp0 hge hmono ht1 (show 1 ≤ i by omega) hti (by rw [← hi]; exact hn.le)]
    exact ENNReal.ofReal_le_one.2 (by
      have : 0 ≤ thresholdProd t i / τ ^ i := by
        have := T_pos hp0 hge i
        have : 0 < τ := lt_of_lt_of_le hp0 hτ
        positivity
      linarith)
  · push Not at hex
    set U := ⋃ n, Icc p (t n)
    have hU : MeasurableSet U := MeasurableSet.iUnion (fun n => measurableSet_Icc)
    rw [← lintegral_inter_add_sdiff (fun x => FF t x) (Icc p τ) hU]
    have h0 : ∫⁻ x in Icc p τ \ U, FF t x = 0 := by
      rw [setLIntegral_congr_fun (measurableSet_Icc.diff hU) (g := fun _ => 0)]
      · simp
      · intro x hx
        apply FF_none
        rintro ⟨i, hi1, hi2⟩
        apply hx.2
        exact mem_iUnion.2 ⟨i + 1, hx.1.1, hi2.le⟩
    rw [h0, add_zero]
    calc ∫⁻ x in Icc p τ ∩ U, FF t x ≤ ∫⁻ x in U, FF t x := lintegral_mono_set inter_subset_right
      _ = ⨆ n, ∫⁻ x in Icc p (t n), FF t x := by
          apply setLIntegral_iUnion_of_directed
          exact (Monotone.directed_le (fun a b hab => Icc_subset_Icc le_rfl (hmono hab)))
      _ ≤ 1 := by
          apply iSup_le
          intro n
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h
            rw [ht0, Icc_self, Measure.restrict_singleton]
            simp
          · rw [cumMass_ti hp0 hge hmono ht1 n h]
            exact ENNReal.ofReal_le_one.2 (by
              have : 0 ≤ thresholdProd t n / t n ^ n := by
                have := T_pos hp0 hge n
                have : 0 < t n := lt_of_lt_of_le hp0 (hge n)
                positivity
              linarith)

lemma constraint (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) {τ : ℝ} (hτ : p ≤ τ) (ℓ : ℕ) :
    ENNReal.ofReal (τ * thresholdQ t τ ℓ) + ∫⁻ x in Icc p τ, FF t x ≤ 1 := by
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    have hi : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; exact (no_zero ht0 ht1 hi1 hi2).elim
      · exact h0
    rw [cumMass_in hp0 hge hmono ht1 hi hi1 hi2.le, tq_eq hmono hi1 hi2]
    have hτ0 : 0 < τ := lt_of_lt_of_le hp0 hτ
    have hT := T_pos hp0 hge i
    have hc : 0 ≤ thresholdProd t i / τ ^ i := by positivity
    have hc' : thresholdProd t i / τ ^ i ≤ 1 := by
      have h3 : thresholdProd t i / τ ^ i ≤ thresholdProd t i / t i ^ i := by
        have hti : 0 < t i := lt_of_lt_of_le hp0 (hge i)
        apply div_le_div_of_nonneg_left hT.le (by positivity)
        exact pow_le_pow_left₀ hti.le hi1 i
      linarith [T_div_le hp0 hge hmono i]
    split_ifs
    · have : τ * (thresholdProd t i / τ ^ (i + 1)) = thresholdProd t i / τ ^ i := by
        rw [pow_succ]; field_simp
      rw [this, ← ENNReal.ofReal_add hc (by linarith)]
      exact ENNReal.ofReal_le_one.2 (by linarith)
    · rw [mul_zero, ENNReal.ofReal_zero, zero_add]
      exact ENNReal.ofReal_le_one.2 (by linarith)
  · rw [tq_none h, mul_zero, ENNReal.ofReal_zero, zero_add]
    exact cumMass_le_one hp0 hge hmono ht0 ht1 hτ

lemma tq_x_intervalIntegrable (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t)
    (ht0 : t 0 = p) (ht1 : t 1 = p) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => x * thresholdQ t x j) volume a b := by
  apply IntegrableOn.intervalIntegrable
  rw [uIcc_eq_union]
  apply IntegrableOn.union
  · exact IntegrableOn.continuousOn_mul continuousOn_id
      (tq_integrableOn hp0 hge hmono ht0 ht1 j _ _) isCompact_Icc
  · exact IntegrableOn.continuousOn_mul continuousOn_id
      (tq_integrableOn hp0 hge hmono ht0 ht1 j _ _) isCompact_Icc

/-- the integral of `x q(x, j)` over one threshold interval -/
lemma piece (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (i j : ℕ) :
    ∫ x in t i..t (i + 1), x * thresholdQ t x j =
      if j ≤ i then ∫ x in t i..t (i + 1), thresholdProd t i / x ^ i else 0 := by
  have hle : t i ≤ t (i + 1) := hmono (Nat.le_succ i)
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({t (i + 1)} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton)
  have key : ∫ x in t i..t (i + 1), x * thresholdQ t x j =
      ∫ x in t i..t (i + 1), (if j ≤ i then thresholdProd t i / x ^ i else 0) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hxI
    rw [uIoc_of_le hle] at hxI
    have hxb : x < t (i + 1) := lt_of_le_of_ne hxI.2 (by simpa using hx)
    rw [tq_eq hmono hxI.1.le hxb]
    have hx0 : 0 < x := lt_of_lt_of_le hp0 (le_trans (hge i) hxI.1.le)
    split_ifs
    · rw [pow_succ]; field_simp
    · ring
  rw [key]
  split_ifs
  · rfl
  · simp

lemma partial_int (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (j n : ℕ) :
    ∫ x in p..t n, x * thresholdQ t x j =
      ∑ i ∈ Finset.range n, ∫ x in t i..t (i + 1), x * thresholdQ t x j := by
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := t)
    (fun k _ => tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 j _ _), ht0]

/-- pointwise inequality behind Lemma 4 -/
lemma pointwise_Fk (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (k : ℕ) {x : ℝ}
    (hx0 : p ≤ x) (hx1 : x ≤ 1) :
    ∑ j ∈ Finset.Icc 1 k, x * thresholdQ t x j ≤
      ∑ ℓ ∈ Finset.Icc 1 k, thresholdQ t x ℓ * nbTerm k ℓ x := by
  have hxp : 0 < x := lt_of_lt_of_le hp0 hx0
  have hnn : ∀ i, 0 ≤ thresholdProd t i / x ^ (i + 1) := fun i => by
    have := T_pos hp0 hge i; positivity
  unfold nbTerm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 k) (s' := fun j => Finset.Icc 1 j)]
  · apply Finset.sum_le_sum
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hb4 := b4_binomial_identity j hj1 x ⟨hxp.le, hx1⟩
    calc x * thresholdQ t x j = thresholdQ t x j *
          ∑ ℓ ∈ Finset.Icc 1 j, ((j - 1).choose (ℓ - 1) : ℝ) * (1 - x) ^ (j - ℓ) * x ^ ℓ := by
          rw [hb4]; ring
      _ = ∑ ℓ ∈ Finset.Icc 1 j, thresholdQ t x j *
          (((j - 1).choose (ℓ - 1) : ℝ) * (1 - x) ^ (j - ℓ) * x ^ ℓ) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓj : ℓ ≤ j := (Finset.mem_Icc.1 hℓ).2
          have hc : 0 ≤ ((j - 1).choose (ℓ - 1) : ℝ) * (1 - x) ^ (j - ℓ) * x ^ ℓ := by
            have : 0 ≤ 1 - x := by linarith
            positivity
          exact mul_le_mul_of_nonneg_right (tq_anti hmono x hℓj hnn) hc
  · intro ℓ j
    simp only [Finset.mem_Icc]
    omega

end generic


section specific

variable {p α : ℝ}

lemma gamma_diff (m : ℕ) :
    gammaK p α (m + 1) - gammaK p α (m + 2) = α * ((m : ℝ) + 1) * p ^ m * (1 - p) ^ 2 := by
  simp only [gammaK]
  have e1 : m + 1 - 1 = m := by omega
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e1, e2]
  push_cast
  ring

/-- value of each piece for Lemma 6's sequence: `α(1-p)^2 p^{i-1}` -/
lemma piece_val (hp : p ∈ Ioo (0:ℝ) 1) (hα : α ∈ Ioo (0:ℝ) 1)
    (hge : ∀ i, p ≤ tSeq p α i) (i : ℕ) (hi : 1 ≤ i) :
    ∫ x in tSeq p α i..tSeq p α (i + 1), thresholdProd (tSeq p α) i / x ^ i =
      α * (1 - p) ^ 2 * p ^ (i - 1) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hmono_i : tSeq p α i ≤ tSeq p α (i + 1) := lemma_6_i p α ⟨hp0, hp1⟩ hα i hi
  have hti : 0 < tSeq p α i := lt_of_lt_of_le hp0 (hge i)
  rcases Nat.lt_or_ge i 2 with h | h
  · -- i = 1
    have hi1 : i = 1 := by omega
    subst hi1
    have hT : thresholdProd (tSeq p α) 1 = p := by unfold thresholdProd; simp [tSeq]
    have h1 : tSeq p α 1 = p := by simp [tSeq]
    have h2 : tSeq p α (1 + 1) = p * Real.exp (α * (1 - p) ^ 2 / p) := by simp [tSeq]
    rw [hT]
    simp only [pow_one, Nat.sub_self, pow_zero, mul_one]
    rw [show (fun x : ℝ => p / x) = fun x => p * (1 / x) by funext x; ring]
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos (by rw [h1]; exact hp0)
      (by rw [h2]; positivity), h1, h2]
    rw [mul_div_cancel_left₀ _ hp0.ne', Real.log_exp]
    field_simp
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    set t := tSeq p α
    set T := thresholdProd t (m + 2)
    have hb6a := b6_product_identity p α ⟨hp0, hp1⟩ hα (m + 2) (by omega)
    have hb6b := b6_product_identity p α ⟨hp0, hp1⟩ hα (m + 3) (by omega)
    simp only [show m + 2 - 1 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega] at hb6a hb6b
    have hti1 : 0 < t (m + 3) := lt_of_lt_of_le hp0 (hge (m + 3))
    have hTs : thresholdProd t (m + 3) = T * t (m + 3) := T_succ (m + 2)
    rw [hTs] at hb6b
    -- antiderivative
    have hint : ∫ x in t (m + 2)..t (m + 2 + 1), T / x ^ (m + 2) =
        (1 / ((m : ℝ) + 1)) * (T / t (m + 2) ^ (m + 1) - T / t (m + 3) ^ (m + 1)) := by
      have hfun : (fun x : ℝ => T / x ^ (m + 2)) =
          fun x => (1 / ((m : ℝ) + 1)) * (((m + 1 : ℕ) : ℝ) * (T / x ^ (m + 1 + 1))) := by
        funext x; push_cast; field_simp
      rw [hfun, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -(T / x ^ (m + 1)))]
      · ring
      · intro x hx
        rw [uIcc_of_le hmono_i] at hx
        exact hasDeriv_Tpow T (m + 1) (by omega) x (lt_of_lt_of_le hti hx.1)
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.div continuousOn_const (continuousOn_pow _)
        intro x hx
        rw [uIcc_of_le hmono_i] at hx
        exact pow_ne_zero _ (lt_of_lt_of_le hti hx.1).ne'
    rw [hint]
    have e1 : T / t (m + 2) ^ (m + 1) = p * gammaK p α (m + 1) := hb6a
    have e2 : T / t (m + 3) ^ (m + 1) = p * gammaK p α (m + 2) := by
      have hne : t (m + 3) ≠ 0 := hti1.ne'
      rw [← hb6b, show tSeq p α (m + 3) = t (m + 3) from rfl, pow_succ]
      field_simp
      ring
    rw [e1, e2, ← mul_sub, gamma_diff]
    simp only [show m + 2 - 1 = m + 1 by omega]
    field_simp
    ring

end specific

end L6iiiAux

open L6iiiAux SampleDrivenOS.Limit SampleDrivenOS.Structure in
theorem solution (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1)
    (h18 : Real.log p + α * (1 - p) ^ 2 / p ≤
      ∑' i : ℕ, Real.log (SampleDrivenOS.Limit.gammaK p α (i + 2)) / (((i : ℝ) + 1) * ((i : ℝ) + 2))) :
    SampleDrivenOS.Limit.IsSDFeasible p (SampleDrivenOS.Limit.thresholdQ (SampleDrivenOS.Limit.tSeq p α)) α := by
  obtain ⟨hp0, hp1⟩ := hp
  have ht0 : tSeq p α 0 = p := by simp [tSeq]
  have ht1 : tSeq p α 1 = p := by simp [tSeq]
  have hmono : Monotone (tSeq p α) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [ht0, ht1]
    · exact lemma_6_i p α ⟨hp0, hp1⟩ hα n h
  have hge : ∀ i, p ≤ tSeq p α i := fun i => ht0 ▸ hmono (Nat.zero_le i)
  have hle1 : ∀ i, tSeq p α i ≤ 1 := by
    obtain ⟨L, hL, hL1, -⟩ := lemma_6_ii p α ⟨hp0, hp1⟩ hα
    intro i
    exact le_trans (hmono.ge_of_tendsto hL i) (hL1.2 h18)
  set t := tSeq p α with ht_def
  refine ⟨⟨?_, ?_, ?_⟩, hα.1.le, hα.2.le, ?_⟩
  · intro τ _ ℓ _
    exact tq_nonneg hp0 hge hmono τ ℓ
  · intro ℓ _
    exact tq_integrableOn hp0 hge hmono ht0 ht1 ℓ p 1
  · intro τ hτ ℓ _
    have := constraint hp0 hge hmono ht0 ht1 hτ.1 ℓ
    rw [cumMass_eq_lint (thresholdQ t) rfl τ]
    exact this
  · intro k hk
    have hpk : 0 < 1 - p ^ k := by
      have : p ^ k < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
      linarith
    rw [le_div_iff₀ hpk]
    -- lower bound for each `∫_p^1 x q(x, j)`
    have hj : ∀ j : ℕ, α * (1 - p) * p ^ j ≤ ∫ x in p..1, x * thresholdQ t x (j + 1) := by
      intro j
      have hpart : ∀ m : ℕ, ∫ x in p..t (j + 1 + m), x * thresholdQ t x (j + 1) =
          α * (1 - p) * p ^ j * (1 - p ^ m) := by
        intro m
        rw [partial_int hp0 hge hmono ht0 ht1]
        induction m with
        | zero =>
          simp only [add_zero, pow_zero, sub_self, mul_zero]
          apply Finset.sum_eq_zero
          intro i hi
          rw [piece hp0 hge hmono, if_neg (by simp at hi; omega)]
        | succ m ih =>
          rw [show j + 1 + (m + 1) = (j + 1 + m) + 1 by omega, Finset.sum_range_succ, ih,
            piece hp0 hge hmono, if_pos (by omega),
            piece_val ⟨hp0, hp1⟩ hα hge _ (by omega)]
          simp only [show j + 1 + m - 1 = j + m by omega]
          ring
      have hlim : Tendsto (fun m : ℕ => α * (1 - p) * p ^ j * (1 - p ^ m)) atTop
          (𝓝 (α * (1 - p) * p ^ j * (1 - 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.sub
          (tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1))
      rw [sub_zero, mul_one] at hlim
      apply le_of_tendsto' hlim
      intro m
      rw [← hpart m]
      have hn1 := hle1 (j + 1 + m)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 _ p (t (j + 1 + m)))
        (tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 _ (t (j + 1 + m)) 1)]
      have : 0 ≤ ∫ x in t (j + 1 + m)..1, x * thresholdQ t x (j + 1) := by
        apply intervalIntegral.integral_nonneg hn1
        intro x hx
        have hx0 : 0 ≤ x := le_trans hp0.le (le_trans (hge _) hx.1)
        exact mul_nonneg hx0 (tq_nonneg hp0 hge hmono x _)
      linarith
    -- F_k ≥ Σ_j ∫ x q(x,j)
    have hF : ∑ j ∈ Finset.Icc 1 k, ∫ x in p..1, x * thresholdQ t x j ≤ Fk p (thresholdQ t) k := by
      unfold Fk
      have hint1 : ∀ ℓ ∈ Finset.Icc 1 k, IntervalIntegrable
          (fun x => thresholdQ t x ℓ * nbTerm k ℓ x) volume p 1 := by
        intro ℓ _
        apply IntegrableOn.intervalIntegrable
        rw [uIcc_of_le hp1.le]
        apply IntegrableOn.mul_continuousOn (tq_integrableOn hp0 hge hmono ht0 ht1 ℓ p 1) _
          isCompact_Icc
        unfold nbTerm
        fun_prop
      rw [← intervalIntegral.integral_finsetSum
          (fun j _ => tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 j p 1),
        ← intervalIntegral.integral_finsetSum hint1]
      apply intervalIntegral.integral_mono_on hp1.le
      · have h := IntervalIntegrable.sum (Finset.Icc 1 k)
          (fun j _ => tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 j p 1)
        rw [Finset.sum_fn] at h
        exact h
      · have h := IntervalIntegrable.sum (Finset.Icc 1 k) hint1
        rw [Finset.sum_fn] at h
        exact h
      · intro x hx
        exact pointwise_Fk hp0 hge hmono k hx.1 hx.2
    have hsum : ∀ k : ℕ, α * (1 - p ^ k) ≤ ∑ j ∈ Finset.Icc 1 k, ∫ x in p..1, x * thresholdQ t x j := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have := hj n
        have e : α * (1 - p ^ (n + 1)) = α * (1 - p ^ n) + α * (1 - p) * p ^ n := by ring
        linarith
    have := hsum k
    linarith
