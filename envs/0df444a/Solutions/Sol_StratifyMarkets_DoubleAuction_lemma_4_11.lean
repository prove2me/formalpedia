-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:52:35.828191+00:00
-- url     : https://prove2.me/submissions/e66acc67-1a6c-447a-904d-a8602e82d952

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_10
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_6

set_option autoImplicit false

-- Solutions.StratifyMarketsBalancedLaw
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

/-- Equation (4.1) defines the same expected count for all balanced prices,
even when some marginal CDFs are constant on a nonempty interval. -/
theorem balanced_count_unique {n m : ℕ} (I : DAInstance n m) {p q : ℝ}
    (hp : I.IsBalancedPrice p) (hq : I.IsBalancedPrice q) : I.expB p = I.expB q := by
  have hB : Antitone I.expB := by
    intro x y h
    apply Finset.sum_le_sum
    intro i _
    let := I.isProb_B i
    exact measureReal_mono (Ici_subset_Ici.mpr h)
  have hS : Monotone I.expS := by
    intro x y h
    apply Finset.sum_le_sum
    intro j _
    let := I.isProb_S j
    exact measureReal_mono (Iic_subset_Iic.mpr h)
  rcases le_total p q with h | h
  · exact le_antisymm (hp.2.le.trans ((hS h).trans hq.2.ge)) (hB h)
  · exact le_antisymm (hB h) (hq.2.le.trans ((hS h).trans hp.2.ge))

/-- A global price and the same price in the whole unit interval trade with
identical eligible sets almost surely under the product law. -/
theorem whole_submarket_eq {n m : ℕ} (I : DAInstance n m) (p : ℝ) :
    I.worstRationedIn 0 p 1 = I.worstRationed p := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  have B (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 := by
    have h : Icc (0 : ℝ) 1 ∈ ae (I.μB i) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)
    exact (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae h)
  have S (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 := by
    have h : Icc (0 : ℝ) 1 ∈ ae (I.μS j) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)
    exact (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae h)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr B, ae_all_iff.mpr S] with x hx hy
  congr 1
  · ext i
    simp [Finset.mem_filter, (hx i).2]
  · ext j
    simp [Finset.mem_filter, (hy j).1]

/-- Every summand of the efficient matching is positive because the list of
seller costs increases while the list of buyer values decreases. -/
theorem realizedFB_nonnegative {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) :
    0 ≤ realizedFB v c := by
  apply Finset.sum_nonneg
  intro i hi
  have hit : i < tau v c := Finset.mem_range.mp hi
  obtain ⟨j, hj, hij⟩ := Finset.lt_sup_iff.mp hit
  obtain ⟨jr, hjgain⟩ := Finset.mem_filter.mp hj
  have jmin := Finset.mem_range.mp jr
  change i < j+1 at hij
  have jv : j < (valuesDesc v).length := by simpa [valuesDesc] using (lt_of_lt_of_le jmin (min_le_left n m))
  have js : j < (costsAsc c).length := by simpa [costsAsc] using (lt_of_lt_of_le jmin (min_le_right n m))
  have ig : i ≤ j := Nat.le_of_lt_succ hij
  change (costsAsc c).getD j 0 < (valuesDesc v).getD j 0 at hjgain
  apply sub_nonneg.mpr
  rcases eq_or_lt_of_le ig with rfl | hl
  · exact hjgain.le
  have cv := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≥ ·) (List.ofFn v))
    i j (ig.trans_lt jv) jv hl
  have cc := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≤ ·) (List.ofFn c))
    i j (ig.trans_lt js) js hl
  simp only [List.getD_eq_getElem _ _ jv, List.getD_eq_getElem _ _ js] at hjgain
  rw [List.getD_eq_getElem _ _ (ig.trans_lt js), List.getD_eq_getElem _ _ (ig.trans_lt jv)]
  exact cc.trans (hjgain.le.trans cv)

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsFirstBest
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

private theorem sorted_coordinate_measurable {k : ℕ} (r : ℝ → ℝ → Bool)
    (hr : ∀ i j : Fin k, Measurable fun v : Fin k → ℝ => r (v i) (v j))
    (t : ℕ) :
    Measurable fun v : Fin k → ℝ => ((List.ofFn v).mergeSort r).getD t 0 := by
  let table := fun (v : Fin k → ℝ) (i j : Fin k) => r (v i) (v j)
  have htable : Measurable table :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hr i j
  let indices := List.ofFn (id : Fin k → Fin k)
  let entry := fun (z : (Fin k → ℝ) × (Fin k → Fin k → Bool)) =>
    (((indices.mergeSort z.2).map z.1)[t]?).getD 0
  have hentry : Measurable entry := by
    apply measurable_from_prod_countable_left
    intro order
    simp only [entry, List.getElem?_map]
    cases (indices.mergeSort order)[t]? with
    | none => exact measurable_const
    | some i => exact measurable_pi_apply i
  have hmap (v : Fin k → ℝ) :
      (indices.mergeSort (table v)).map v = (List.ofFn v).mergeSort r := by
    simpa [indices, List.map_ofFn] using
      (List.map_mergeSort (f := v) (l := indices) (r := table v) (s := r)
        (fun _ _ _ _ => rfl))
  simpa only [Function.comp_def, id_eq, entry, hmap, List.getD_eq_getElem?_getD] using
    hentry.comp (measurable_id.prodMk htable)

theorem measurable_trade_cut {n m : ℕ} (r : ℕ) :
    MeasurableSet {x : (Fin n → ℝ) × (Fin m → ℝ) | r < tau x.1 x.2} := by
  have value (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun v : Fin n → ℝ => v b) (g := fun v => v a)
          (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have cost (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun c : Fin m → ℝ => c a) (g := fun c => c b)
          (measurable_pi_apply a) (measurable_pi_apply b)))) i
  let trades := fun i => {x : (Fin n → ℝ) × (Fin m → ℝ) |
    (costsAsc x.2).getD i 0 < (valuesDesc x.1).getD i 0}
  have h : {x : (Fin n → ℝ) × (Fin m → ℝ) | r < tau x.1 x.2} =
      ⋃ i : ℕ, ⋃ (_ : i < min n m ∧ r < i + 1), trades i := by
    ext x
    simp [tau, Finset.lt_sup_iff, trades]
    aesop
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    measurableSet_lt ((cost i).comp measurable_snd) ((value i).comp measurable_fst)


theorem integrable_first_best {n m : ℕ} (I : DAInstance n m) :
    Integrable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2) I.law := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  have count (v : Fin n → ℝ) (c : Fin m → ℝ) : tau v c ≤ min n m := by
    apply Finset.sup_le
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hv (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using (measurableSet_le (f := fun v : Fin n → ℝ => v b)
        (g := fun v => v a) (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have hc (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using (measurableSet_le (f := fun c : Fin m → ℝ => c a)
        (g := fun c => c b) (measurable_pi_apply a) (measurable_pi_apply b)))) i
  have hmeas : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2) := by
    have expand (v : Fin n → ℝ) (c : Fin m → ℝ) :
        realizedFB v c = ∑ i ∈ Finset.range (min n m), if i < tau v c then
          (valuesDesc v).getD i 0 - (costsAsc c).getD i 0 else 0 := by
      rw [← Finset.sum_filter]
      unfold realizedFB
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => ⟨h.trans_le (count v c), h⟩, fun h => h.2⟩
    simp_rw [expand]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite (measurable_trade_cut i)
      (((hv i).comp measurable_fst).sub ((hc i).comp measurable_snd)) measurable_const
  have B (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have S (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (min n m : ℕ)
  filter_upwards [ae_all_iff.mpr B, ae_all_iff.mpr S] with x hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg (realizedFB_nonnegative _ _)]
  have entry {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool) (h : ∀ j, w j ∈ Icc (0 : ℝ) 1)
      (i : ℕ) (hi : i < k) : ((List.ofFn w).mergeSort r).getD i 0 ∈ Icc (0 : ℝ) 1 := by
    have hil : i < ((List.ofFn w).mergeSort r).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hil]
    have mem := List.getElem_mem (l := (List.ofFn w).mergeSort r) hil
    have orig := List.mem_mergeSort.mp mem
    obtain ⟨j,hj⟩ := (List.mem_ofFn' _ _).mp orig
    rw [← hj]
    exact h j
  calc
    realizedFB x.1 x.2 ≤ ∑ _i ∈ Finset.range (tau x.1 x.2), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (Finset.mem_range.mp hi).trans_le (count x.1 x.2)
      have hb := (entry x.1 (fun a b => decide (b ≤ a)) hx i (h.trans_le (min_le_left _ _))).2
      have hs := (entry x.2 (fun a b => decide (a ≤ b)) hy i (h.trans_le (min_le_right _ _))).1
      change (valuesDesc x.1).getD i 0 ≤ 1 at hb
      change 0 ≤ (costsAsc x.2).getD i 0 at hs
      linarith
    _ ≤ _ := by simpa using (show (tau x.1 x.2 : ℝ) ≤ (min n m : ℕ) by exact_mod_cast count x.1 x.2)

theorem sorted_positive_sum {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool)
    (φ : ℝ → ℝ) (hφ : ∀ a, 0 ≤ φ a) {t : ℕ} (ht : t ≤ k) :
    (∑ i ∈ Finset.range t, φ (((List.ofFn w).mergeSort r).getD i 0)) ≤ ∑ i, φ (w i) := by
  let l := (List.ofFn w).mergeSort r
  have len : l.length = k := by simp [l]
  have hperm := (List.mergeSort_perm (List.ofFn w) r).map φ
  calc
    _ ≤ ∑ i ∈ Finset.range l.length, φ (l.getD i 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (ht.trans_eq len.symm)) (fun i _ _ => hφ _)
    _ = (l.map φ).sum := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [← List.sum_ofFn]
      congr 1
      rw [← List.ofFn_getElem_eq_map]
      apply congrArg List.ofFn
      funext i
      rw [List.getD_eq_getElem _ _ i.isLt]
    _ = ((List.ofFn w).map φ).sum := hperm.sum_eq
    _ = ∑ i, φ (w i) := by simp [List.map_ofFn, List.sum_ofFn]

theorem realized_surplus {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (t : ℝ) :
    realizedFB v c ≤ ∑ i, max (v i - t) 0 + ∑ j, max (t - c j) 0 := by
  have H : tau v c ≤ min n m := by
    apply Finset.sup_le
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  calc
    _ ≤ ∑ i ∈ Finset.range (tau v c), (max ((valuesDesc v).getD i 0 - t) 0 + max (t - (costsAsc c).getD i 0) 0) := by
      apply Finset.sum_le_sum
      intro i _
      linarith only [le_max_left ((valuesDesc v).getD i 0 - t) 0, le_max_left (t - (costsAsc c).getD i 0) 0]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (sorted_positive_sum v (fun a b => decide (b ≤ a)) (fun x => max (x-t) 0)
        (fun _ => le_max_right _ _) (H.trans (min_le_left _ _)))
        (sorted_positive_sum c (fun a b => decide (a ≤ b)) (fun x => max (t-x) 0)
          (fun _ => le_max_right _ _) (H.trans (min_le_right _ _)))

end StratifyMarkets.DoubleAuction
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_11
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

private theorem exists_balancedPrice {n m : ℕ} (I : DAInstance n m) :
    ∃ p, I.IsBalancedPrice p := by
  have buyers_cont : ContinuousOn I.expB (Icc 0 1) := by
    unfold DAInstance.expB
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    let := I.isProb_B i
    let := I.noAtoms_B i
    have h : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ici 0) (I.μB i) :=
      (integrable_const 1).integrableOn
    simpa only [setIntegral_one_eq_measureReal, measureReal_def] using
      (h.continuousOn_Ici_primitive_Ici.mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from Icc_subset_Ici_self))
  have sellers_cont : ContinuousOn I.expS (Icc 0 1) := by
    unfold DAInstance.expS
    refine continuousOn_finsetSum _ fun j _ ↦ ?_
    let := I.isProb_S j
    let := I.noAtoms_S j
    have h : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Iic 1) (I.μS j) :=
      (integrable_const 1).integrableOn
    simpa only [setIntegral_one_eq_measureReal, measureReal_def] using
      (h.continuousOn_Iic_primitive_Iic.mono (show Icc (0 : ℝ) 1 ⊆ Iic 1 from Icc_subset_Iic_self))
  have buyers_at_one : I.expB 1 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    let := I.isProb_B i
    let := I.noAtoms_B i
    have h := (prob_compl_eq_zero_iff measurableSet_Icc).2 (I.support_B i)
    have ho : I.μB i (Ioi 1) = 0 :=
      measure_mono_null (t := (Icc (0 : ℝ) 1)ᶜ) (fun _ hx hmem ↦ (not_lt_of_ge hmem.2) hx) h
    rw [← measure_congr Ioi_ae_eq_Ici, ho, ENNReal.toReal_zero]
  have sellers_at_zero : I.expS 0 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    let := I.isProb_S j
    let := I.noAtoms_S j
    have h := (prob_compl_eq_zero_iff measurableSet_Icc).2 (I.support_S j)
    have ho : I.μS j (Iio 0) = 0 :=
      measure_mono_null (t := (Icc (0 : ℝ) 1)ᶜ) (fun _ hx hmem ↦ (not_lt_of_ge hmem.1) hx) h
    rw [← measure_congr Iio_ae_eq_Iic, ho, ENNReal.toReal_zero]
  apply isPreconnected_Icc.intermediate_value₂ (right_mem_Icc.mpr zero_le_one)
    (left_mem_Icc.mpr zero_le_one) buyers_cont sellers_cont
  · rw [buyers_at_one]
    exact Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  · rw [sellers_at_zero]
    exact Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg

theorem solution {n m : ℕ} (I : DAInstance n m) :
    ∃ p ∈ Icc (0 : ℝ) 1,
      (∀ pt : ℝ, I.IsBalancedPrice pt →
        (4 ≤ I.expB pt → 1 / 40 * I.FB ≤ I.worstRationedIn 0 p 1) ∧
        (I.expB pt < 4 → 1 / 7 * I.FBtauGt5 ≤ I.worstRationedIn 0 p 1)) ∧
      1 / 40 * I.FBtauGt5 ≤ I.worstRationedIn 0 p 1 := by
  have hm : Integrable (fun x => if 5 < tau x.1 x.2 then realizedFB x.1 x.2 else 0) I.law := by
    have hit := (integrable_first_best I).indicator (measurable_trade_cut 5)
    apply hit.congr
    apply Filter.Eventually.of_forall
    intro x
    simp [Set.indicator]
  have bounded : I.FBtauGt5 ≤ I.FB := by
    apply integral_mono hm (integrable_first_best I)
    intro x
    change (if _ then _ else 0) ≤ realizedFB x.1 x.2
    split_ifs
    · exact le_rfl
    · exact realizedFB_nonnegative _ _
  have hpos : 0 ≤ I.FBtauGt5 := by
    apply integral_nonneg
    intro x
    change 0 ≤ (if _ then _ else (0:ℝ))
    split_ifs
    · exact realizedFB_nonnegative _ _
    · exact le_rfl
  obtain ⟨q,hq⟩ := exists_balancedPrice I
  rcases le_or_gt 4 (I.expB q) with h | h
  · obtain ⟨p,hp,hw⟩ := lemma_4_6 I q hq h
    rw [← whole_submarket_eq I p] at hw
    refine ⟨p, hp, fun t ht => ⟨fun _ => hw, fun h' => ?_⟩, by linarith⟩
    linarith [balanced_count_unique I hq ht]
  · have hw := lemma_4_10 I q hq h
    rw [← whole_submarket_eq I q] at hw
    refine ⟨q, hq.1, fun t ht => ⟨fun h' => ?_, fun _ => hw⟩, by linarith⟩
    linarith [balanced_count_unique I hq ht]
end
