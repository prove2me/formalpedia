-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:57:26.224204+00:00
-- url     : https://prove2.me/submissions/2e31800f-bf46-43dc-a217-3a5df2eafbd1

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_11
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_20

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_theorem_4_1
section
open MeasureTheory Set

namespace StratifyMarkets.DoubleAuction

/-- Under atomless laws supported on `[0, 1]`, some price balances the expected
numbers of eligible buyers and sellers. This also holds when either side is empty. -/
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

end StratifyMarkets.DoubleAuction

namespace StratifyMarkets.DoubleAuction

-- Once the finite table of pairwise comparisons is fixed, sorting simply
-- selects a coordinate (or the default value for an out-of-range index).
private theorem measurable_sorted_entry {k : ℕ} (r : ℝ → ℝ → Bool)
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

private theorem measurable_many_trades {n m : ℕ} :
    MeasurableSet {x : (Fin n → ℝ) × (Fin m → ℝ) | 5 < tau x.1 x.2} := by
  have value (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    measurable_sorted_entry (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun v : Fin n → ℝ => v b) (g := fun v => v a)
          (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have cost (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    measurable_sorted_entry (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun c : Fin m → ℝ => c a) (g := fun c => c b)
          (measurable_pi_apply a) (measurable_pi_apply b)))) i
  let trades := fun i => {x : (Fin n → ℝ) × (Fin m → ℝ) |
    (costsAsc x.2).getD i 0 < (valuesDesc x.1).getD i 0}
  have h : {x : (Fin n → ℝ) × (Fin m → ℝ) | 5 < tau x.1 x.2} =
      ⋃ i : ℕ, ⋃ (_ : i < min n m ∧ 5 < i + 1), trades i := by
    ext x
    simp [tau, Finset.lt_sup_iff, trades]
    aesop
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    measurableSet_lt ((cost i).comp measurable_snd) ((value i).comp measurable_fst)

private theorem fb_split {n m : ℕ} (I : DAInstance n m) (hpos : 0 < I.FB) :
    I.FB = I.FBtauGt5 + I.FBtauLe5 := by
  let s := {x : (Fin n → ℝ) × (Fin m → ℝ) | 5 < tau x.1 x.2}
  let f := fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2
  have hs : MeasurableSet s := measurable_many_trades
  have hfi : Integrable f I.law := Integrable.of_integral_ne_zero hpos.ne'
  have h := (integral_add_compl hs hfi).symm
  rw [← integral_indicator hs, ← integral_indicator hs.compl] at h
  simpa [DAInstance.FB, DAInstance.FBtauGt5, DAInstance.FBtauLe5,
    s, f, Set.indicator, not_lt] using h

end StratifyMarkets.DoubleAuction

open StratifyMarkets.DoubleAuction

private noncomputable def fullBand (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Stratification where
  N := 1
  one_le_N := le_rfl
  m := fun k => (k.val : ℝ)
  p := fun _ => p
  zero_le_m := by norm_num
  m_le_one := by norm_num [Fin.last]
  m_strictMono := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact Nat.cast_lt.mpr (show i.val < j.val from hij)
  p_mem := by
    intro k
    fin_cases k
    simpa using hp

private theorem strat_fullBand {n m : ℕ} (I : DAInstance n m)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    I.strat (fullBand p hp) = I.worstRationedIn 0 p 1 := by
  change (∑ k : Fin 1, I.worstRationedIn (k.val : ℝ) p ((k.val + 1 : ℕ) : ℝ)) =
    I.worstRationedIn 0 p 1
  rw [Fin.sum_univ_one]
  norm_num

private theorem zero_price_nonneg {n m : ℕ} (I : DAInstance n m) :
    0 ≤ I.worstRationedIn 0 0 1 := by
  classical
  unfold DAInstance.worstRationedIn
  apply integral_nonneg
  intro x
  unfold worstRationedGains
  apply Finset.le_inf'
  intro T hT
  obtain ⟨hB, hS⟩ := Finset.mem_product.mp hT
  apply sub_nonneg.mpr
  apply le_trans (b := 0)
  · apply Finset.sum_nonpos
    intro j hj
    exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hS).1 hj)).2.2
  · apply Finset.sum_nonneg
    intro i hi
    exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hB).1 hi)).2.1

theorem solution {n m : ℕ} (I : DAInstance n m) :
    ∃ σ : Stratification, 1 / 27843 * I.FB ≤ I.strat σ := by
  classical
  by_cases hpos : 0 < I.FB
  · obtain ⟨pt, hpt⟩ := exists_balancedPrice I
    obtain ⟨p, hp, hbranches, _⟩ := lemma_4_11 I
    obtain ⟨hlarge, hsmall⟩ := hbranches pt hpt
    rcases le_or_gt 4 (I.expB pt) with hcount | hcount
    · refine ⟨fullBand p hp, ?_⟩
      rw [strat_fullBand]
      linarith only [hlarge hcount, hpos]
    · obtain ⟨σ, hσ⟩ := lemma_4_20 I
      have hk : (0 : ℝ) < 10240 * Real.exp 1 := by positivity
      have hfew : I.FBtauLe5 ≤ I.strat σ * (10240 * Real.exp 1) := by
        apply (div_le_iff₀ hk).mp
        simpa [div_eq_mul_inv, mul_comm] using hσ
      have hmany : I.FBtauGt5 ≤ 7 * I.strat (fullBand p hp) := by
        rw [strat_fullBand]
        linarith only [hsmall hcount]
      obtain ⟨best, hone, htwo⟩ : ∃ best : Stratification,
          I.strat (fullBand p hp) ≤ I.strat best ∧ I.strat σ ≤ I.strat best := by
        rcases le_total (I.strat (fullBand p hp)) (I.strat σ) with h | h
        · exact ⟨σ, h, le_rfl⟩
        · exact ⟨fullBand p hp, le_rfl, h⟩
      refine ⟨best, ?_⟩
      have htotal : I.FB ≤ (7 + 10240 * Real.exp 1) * I.strat best := calc
        I.FB = I.FBtauGt5 + I.FBtauLe5 := fb_split I hpos
        _ ≤ 7 * I.strat (fullBand p hp) + I.strat σ * (10240 * Real.exp 1) :=
          add_le_add hmany hfew
        _ ≤ 7 * I.strat best + I.strat best * (10240 * Real.exp 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hone (by norm_num))
            (mul_le_mul_of_nonneg_right htwo hk.le)
        _ = (7 + 10240 * Real.exp 1) * I.strat best := by ring
      have hbest : 0 ≤ I.strat best :=
        nonneg_of_mul_nonneg_right (hpos.le.trans htotal) (by positivity)
      have hconstant : 7 + 10240 * Real.exp 1 ≤ (27843 : ℝ) := by
        linarith only [Real.exp_one_lt_d9]
      have hbound := htotal.trans (mul_le_mul_of_nonneg_right hconstant hbest)
      linarith only [hbound]
  · have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    refine ⟨fullBand 0 hzero, ?_⟩
    rw [strat_fullBand]
    linarith only [le_of_not_gt hpos, zero_price_nonneg I]
end
