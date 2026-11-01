-- Prove2me | solution 1 for OverflowBinPacking.IID.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:30:54.891227+00:00
-- url     : https://prove2.me/submissions/dfdf3bc5-cbe5-49fb-8223-62bab9f98bce

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Model

open MeasureTheory OverflowBinPacking.IID

namespace OBPX

variable {n : ℕ}

lemma usage_succ (a : Rule n) (x : Fin n → ℝ) (j : Fin n) (i : Fin n) :
    usage a x j (i.val + 1) = usage a x j i.val + (if a i x = j then x i else 0) := by
  classical
  unfold usage
  simp_rw [Finset.sum_filter]
  have : ∀ k : Fin n, (if (k : ℕ) < i.val + 1 ∧ a k x = j then x k else 0) =
      (if (k : ℕ) < i.val ∧ a k x = j then x k else 0) +
        (if i = k then (if a k x = j then x k else 0) else 0) := by
    intro k
    by_cases hik : i = k
    · subst hik; simp
    · have : (k : ℕ) ≠ i.val := fun h => hik (Fin.ext h.symm)
      by_cases hk : (k : ℕ) < i.val
      · simp [hk, hik, show (k : ℕ) < i.val + 1 by omega]
      · simp [hk, hik, show ¬ (k : ℕ) < i.val + 1 by omega]
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

lemma usage_zero (a : Rule n) (x : Fin n → ℝ) (j : Fin n) : usage a x j 0 = 0 := by
  unfold usage; simp

lemma usage_mono (a : Rule n) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) (j : Fin n) {s t : ℕ}
    (hst : s ≤ t) : usage a x j s ≤ usage a x j t := by
  unfold usage
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro k _ _; exact hx k

lemma usage_nonneg (a : Rule n) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) (j : Fin n) (t : ℕ) :
    0 ≤ usage a x j t := by
  unfold usage; exact Finset.sum_nonneg (fun k _ => hx k)

/-- Deterministic identity: a bin breaks iff exactly one item overflows it. -/
lemma card_overflow_items (a : Rule n) (ha : Feasible a) (x : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k)
    (j : Fin n) :
    (Finset.univ.filter (fun i : Fin n => a i x = j ∧ 1 < usage a x j i + x i)).card =
      if 1 < usage a x j n then 1 else 0 := by
  classical
  set F := Finset.univ.filter (fun i : Fin n => a i x = j ∧ 1 < usage a x j i + x i) with hF
  have hmemF : ∀ i, i ∈ F ↔ a i x = j ∧ 1 < usage a x j i + x i := by
    intro i; simp [hF]
  have hsucc : ∀ i : Fin n, a i x = j → usage a x j (i.val + 1) = usage a x j i + x i := by
    intro i hi; rw [usage_succ]; simp [hi]
  have hle1 : F.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi i' hi'
    rw [hmemF] at hi hi'
    by_contra hne
    have key : ∀ i i' : Fin n, a i x = j ∧ 1 < usage a x j i + x i →
        a i' x = j → i < i' → False := by
      intro i i' hi hi' hlt
      have h1 := hsucc i hi.1
      have h2 := usage_mono a x hx j (show i.val + 1 ≤ i'.val by omega)
      have h3 := ha x i'
      rw [hi'] at h3
      linarith [hi.2]
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i i' hi hi'.1 h
    · exact key i' i hi' hi.1 h
  split_ifs with hb
  · apply le_antisymm hle1
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    -- find the first time the load exceeds one
    have hex : ∃ t, 1 < usage a x j t := ⟨n, hb⟩
    let t := Nat.find hex
    have ht : 1 < usage a x j t := Nat.find_spec hex
    have htn : t ≤ n := Nat.find_min' hex hb
    have ht0 : t ≠ 0 := by
      intro h0; rw [show t = 0 from h0, usage_zero] at ht; linarith
    obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hsn : s < n := by omega
    have hsle : ¬ 1 < usage a x j s := Nat.find_min hex (by omega)
    have := usage_succ a x j ⟨s, hsn⟩
    simp only at this
    rw [← hs] at this
    by_cases has : a ⟨s, hsn⟩ x = j
    · refine ⟨⟨s, hsn⟩, (hmemF _).mpr ⟨has, ?_⟩⟩
      simp only [has, if_true] at this
      simp only
      linarith
    · simp only [has, if_false, add_zero] at this
      exact absurd (this ▸ ht) hsle
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [hmemF] at hi
    have h1 := hsucc i hi.1
    have h2 := usage_mono a x hx j (show i.val + 1 ≤ n by omega)
    exact hb (by linarith [hi.2])

lemma measurable_usage (a : Rule n) (ha : MeasurableRule a) (j : Fin n) (t : ℕ) :
    Measurable (fun x => usage a x j t) := by
  classical
  unfold usage
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.ite ?_ (measurable_pi_apply k) measurable_const
  by_cases hk : (k : ℕ) < t
  · simpa [hk] using ha k j
  · simp [hk]

lemma measurable_overflowProb' (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measurable (fun S : ℝ => overflowProb ν S) := by
  apply Monotone.measurable
  intro a b hab
  unfold overflowProb
  apply measureReal_mono
  · intro z hz; simp only [Set.mem_Ioi] at hz ⊢; linarith
  · exact measure_ne_top _ _

/-- Freezing coordinate `i`: integrating the overflow indicator of item `i` against
quantities not depending on `x i` yields the overflow probability. -/
lemma freeze (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i)) (i : Fin n)
    (P : (Fin n → ℝ) → Prop) [DecidablePred P] (hP : MeasurableSet {x | P x})
    (hPinv : ∀ x t, P (Function.update x i t) ↔ P x)
    (h : (Fin n → ℝ) → ℝ) (hh : Measurable h) (hhinv : ∀ x t, h (Function.update x i t) = h x) :
    ∫⁻ x, (if P x ∧ 1 < h x + x i then (1 : ENNReal) else 0) ∂(Measure.pi μ) =
      ∫⁻ x, (if P x then ENNReal.ofReal (overflowProb (μ i) (h x)) else 0) ∂(Measure.pi μ) := by
  classical
  apply lintegral_eq_of_lmarginal_eq {i}
  · refine Measurable.ite (hP.inter (measurableSet_lt measurable_const
      (hh.add (measurable_pi_apply i)))) measurable_const measurable_const
  · refine Measurable.ite hP (ENNReal.measurable_ofReal.comp
      ((measurable_overflowProb' (μ i)).comp hh)) measurable_const
  · funext x
    rw [lmarginal_singleton, lmarginal_singleton]
    simp only [hPinv, hhinv, Function.update_self]
    by_cases hPx : P x
    · simp only [hPx, true_and, if_true, lintegral_const, measure_univ, mul_one]
      have : (fun t : ℝ => if 1 < h x + t then (1 : ENNReal) else 0) =
          (Set.Ioi (1 - h x)).indicator 1 := by
        funext t
        simp only [Set.indicator, Set.mem_Ioi, Pi.one_apply]
        congr 1; apply propext; constructor <;> intro <;> linarith
      rw [this, lintegral_indicator_one measurableSet_Ioi, overflowProb,
        ofReal_measureReal (measure_ne_top _ _)]
    · simp [hPx]

end OBPX

namespace OBPX

variable {n : ℕ}

lemma ae_nonneg (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0) :
    ∀ᵐ x ∂(Measure.pi μ), ∀ k, 0 ≤ x k := by
  rw [ae_all_iff]
  intro k
  have : Measure.pi μ (Function.eval k ⁻¹' Set.Iio 0) = 0 :=
    Measure.pi_eval_preimage_null μ (hμ0 k)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with x hx
  simpa using hx

lemma usage_update_self (a : Rule n) (ha : Nonanticipative a) (x : Fin n → ℝ) (j i : Fin n)
    (t : ℝ) : usage a (Function.update x i t) j i = usage a x j i := by
  classical
  unfold usage
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : (k : ℕ) < i.val
  · have hne : k ≠ i := fun e => by rw [e] at hk; exact lt_irrefl _ hk
    have h1 : a k (Function.update x i t) = a k x := by
      refine ha k _ _ (fun k' hk' => ?_)
      have : k' ≠ i := fun e => by
        rw [e] at hk'; exact absurd (lt_trans hk' (Fin.lt_def.mpr hk)) (lt_irrefl _)
      exact Function.update_of_ne this _ _
    simp [hk, h1, Function.update_of_ne hne]
  · simp [hk]

lemma rule_update_self (a : Rule n) (ha : Nonanticipative a) (x : Fin n → ℝ) (i : Fin n)
    (t : ℝ) : a i (Function.update x i t) = a i x := by
  refine ha i _ _ (fun k' hk' => ?_)
  exact Function.update_of_ne (ne_of_lt hk') _ _

lemma measurable_risk (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (a : Rule n) (ha : MeasurableRule a) (j : Fin n) :
    Measurable (fun x => risk μ a x j) := by
  classical
  unfold risk riskUpTo
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.ite ?_ ((measurable_overflowProb' (μ k)).comp
    (measurable_usage a ha j k)) measurable_const
  simpa using ha k j

lemma risk_eq_sum (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) :
    risk μ a x j = ∑ k : Fin n, if a k x = j then overflowProb (μ k) (usage a x j k) else 0 := by
  classical
  unfold risk riskUpTo
  rw [Finset.sum_filter]
  simp

lemma overflowProb_nonneg (ν : Measure ℝ) (S : ℝ) : 0 ≤ overflowProb ν S := measureReal_nonneg

lemma overflowProb_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : ℝ) :
    overflowProb ν S ≤ 1 := measureReal_le_one

lemma risk_nonneg (μ : Fin n → Measure ℝ) (a : Rule n) (x : Fin n → ℝ) (j : Fin n) :
    0 ≤ risk μ a x j := by
  rw [risk_eq_sum]
  exact Finset.sum_nonneg (fun k _ => by split_ifs <;> simp [overflowProb_nonneg])

lemma per_bin (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0) (a : Rule n) (ha : IsPolicy a) (j : Fin n) :
    Measure.pi μ {x | 1 < usage a x j n} =
      ∫⁻ x, ENNReal.ofReal (risk μ a x j) ∂(Measure.pi μ) := by
  classical
  have hmS : MeasurableSet {x : Fin n → ℝ | 1 < usage a x j n} :=
    measurableSet_lt measurable_const (measurable_usage a ha.2.1 j n)
  have hmeasP : ∀ i : Fin n, MeasurableSet {x : Fin n → ℝ | a i x = j} := fun i => ha.2.1 i j
  calc Measure.pi μ {x | 1 < usage a x j n}
      = ∫⁻ x, (if 1 < usage a x j n then (1 : ENNReal) else 0) ∂(Measure.pi μ) := by
        rw [← lintegral_indicator_one hmS]
        congr 1
    _ = ∫⁻ x, ∑ i : Fin n, (if a i x = j ∧ 1 < usage a x j i + x i then (1 : ENNReal) else 0)
          ∂(Measure.pi μ) := by
        apply lintegral_congr_ae
        filter_upwards [ae_nonneg μ hμ hμ0] with x hx
        have hc := card_overflow_items a ha.2.2 x hx j
        rw [Finset.card_filter] at hc
        have := congrArg (fun m : ℕ => (m : ENNReal)) hc
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at this
        exact this.symm
    _ = ∑ i : Fin n, ∫⁻ x, (if a i x = j ∧ 1 < usage a x j i + x i then (1 : ENNReal) else 0)
          ∂(Measure.pi μ) := by
        refine lintegral_finsetSum _ (fun i _ => ?_)
        exact Measurable.ite ((hmeasP i).inter (measurableSet_lt measurable_const
          ((measurable_usage a ha.2.1 j i).add (measurable_pi_apply i)))) measurable_const
          measurable_const
    _ = ∑ i : Fin n, ∫⁻ x, (if a i x = j then ENNReal.ofReal (overflowProb (μ i)
          (usage a x j i)) else 0) ∂(Measure.pi μ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact freeze μ hμ i (fun x => a i x = j) (hmeasP i)
          (fun x t => by simp only [rule_update_self a ha.1 x i t])
          (fun x => usage a x j i) (measurable_usage a ha.2.1 j i)
          (fun x t => usage_update_self a ha.1 x j i t)
    _ = ∫⁻ x, ∑ i : Fin n, (if a i x = j then ENNReal.ofReal (overflowProb (μ i)
          (usage a x j i)) else 0) ∂(Measure.pi μ) := by
        refine (lintegral_finsetSum _ (fun i _ => ?_)).symm
        exact Measurable.ite (hmeasP i) (ENNReal.measurable_ofReal.comp
          ((measurable_overflowProb' (μ i)).comp (measurable_usage a ha.2.1 j i)))
          measurable_const
    _ = ∫⁻ x, ENNReal.ofReal (risk μ a x j) ∂(Measure.pi μ) := by
        congr 1; funext x
        rw [risk_eq_sum, ENNReal.ofReal_sum_of_nonneg
          (fun k _ => by split_ifs <;> simp [overflowProb_nonneg])]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        split_ifs <;> simp

lemma prop31 (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0) (a : Rule n) (ha : IsPolicy a) :
    (∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage a x j n} =
        ∫ x, risk μ a x j ∂(Measure.pi μ)) ∧
    (∫ x, (numBroken a x : ℝ) ∂(Measure.pi μ)) =
      ∫ x, (∑ j : Fin n, risk μ a x j) ∂(Measure.pi μ) := by
  classical
  have h1 : ∀ j : Fin n, (Measure.pi μ).real {x | 1 < usage a x j n} =
      ∫ x, risk μ a x j ∂(Measure.pi μ) := by
    intro j
    rw [measureReal_def, per_bin μ hμ hμ0 a ha j, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => risk_nonneg μ a x j))
      (measurable_risk μ hμ a ha.2.1 j).aestronglyMeasurable]
  refine ⟨h1, ?_⟩
  have hint : ∀ j : Fin n, Integrable (fun x => risk μ a x j) (Measure.pi μ) := by
    intro j
    refine Integrable.of_bound (measurable_risk μ hμ a ha.2.1 j).aestronglyMeasurable (n : ℝ)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (risk_nonneg μ a x j), risk_eq_sum]
    calc _ ≤ ∑ k : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun k _ => by
            split_ifs
            · exact overflowProb_le_one _ _
            · norm_num)
      _ = n := by simp
  have hB : (fun x => (numBroken a x : ℝ)) =
      fun x => ∑ j : Fin n, ({x | 1 < usage a x j n}).indicator (1 : (Fin n → ℝ) → ℝ) x := by
    funext x
    rw [numBroken, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Set.indicator]
  rw [hB, integral_finsetSum _ (fun j _ => ?_), integral_finsetSum _ (fun j _ => hint j)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_indicator_one (measurableSet_lt measurable_const
      (measurable_usage a ha.2.1 j n)), h1 j]
  · exact (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const
      (measurable_usage a ha.2.1 j n))

end OBPX

open OverflowBinPacking.IID in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C : ℝ) (hC : 1 ≤ C) (a : Rule n) (ha : IsPolicy a) :
    (∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage a x j n} =
        ∫ x, risk μ a x j ∂(Measure.pi μ)) ∧
    (∫ x, (numBroken a x : ℝ) ∂(Measure.pi μ)) =
      ∫ x, (∑ j : Fin n, risk μ a x j) ∂(Measure.pi μ) :=
  OBPX.prop31 μ hμ hμ0 a ha
