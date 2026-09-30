-- Prove2me | solution 1 for SupplyChainTheory.flex_supermodular_expected
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T07:32:41.916622+00:00
-- url     : https://prove2.me/submissions/a3726b09-5942-490b-b3d4-211cca2551b7

import Mathlib
import Definitions.Def_SupplyChainTheory_flexibility

set_option autoImplicit false

open SupplyChainTheory in
lemma fs_lc_off {n : ℕ} {i j : Fin n} (h : (i, j) ∈ longChain n) (hne : i ≠ j) :
    i = finRotate n j := by
  unfold longChain dedicated at h
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.mk.injEq] at h
  rcases h with ⟨k, hk1, hk2⟩ | ⟨k, hk1, hk2⟩
  · exact absurd (hk1.symm.trans hk2) hne
  · subst hk2; exact hk1.symm

open SupplyChainTheory in
lemma fs_bdd {ι : Type*} [Fintype ι] (C : ℝ) (d : ι → ℝ) (E : Finset (ι × ι)) :
    BddAbove {v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j} := by
  refine ⟨∑ i, d i, ?_⟩
  rintro v ⟨y, hy, rfl⟩
  exact Finset.sum_le_sum fun i _ => hy.2.2.2 i

open SupplyChainTheory in
lemma fs_nonempty {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 ≤ C) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (E : Finset (ι × ι)) :
    ({v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j} : Set ℝ).Nonempty :=
  ⟨0, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ => by simp [hC],
    fun i => by simp [hd i]⟩, by simp⟩

open SupplyChainTheory in
lemma fs_le_perf {ι : Type*} [Fintype ι] (C : ℝ) (d : ι → ℝ) (E : Finset (ι × ι))
    (y : ι → ι → ℝ) (hy : FlexFeasible C d E y) : ∑ i, ∑ j, y i j ≤ perf C d E :=
  le_csSup (fs_bdd C d E) ⟨y, hy, rfl⟩

open SupplyChainTheory in
lemma fs_sum_le {n : ℕ} (f y1 y2 : Fin n → ℝ) (B : ℝ) (h1 : ∑ i, y1 i ≤ B)
    (h2 : ∑ i, y2 i ≤ B) (hf : (∀ i, f i ≤ y1 i) ∨ (∀ i, f i ≤ y2 i)) : ∑ i, f i ≤ B := by
  rcases hf with hf | hf
  · exact (Finset.sum_le_sum fun i _ => hf i).trans h1
  · exact (Finset.sum_le_sum fun i _ => hf i).trans h2

open SupplyChainTheory in
lemma fs_key {n : ℕ} (C : ℝ) (d : Fin n → ℝ) (E : Finset (Fin n × Fin n))
    (hE : E ⊆ longChain n) (a b : Fin n × Fin n) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b)
    (y1 y2 : Fin n → Fin n → ℝ) (h1 : FlexFeasible C d (E \ {a}) y1)
    (h2 : FlexFeasible C d (E \ {b}) y2) :
    ∑ i, ∑ j, y1 i j + ∑ i, ∑ j, y2 i j ≤ perf C d E + perf C d (E \ {a, b}) := by
  -- zeros off E and off the long chain
  have z1E : ∀ i j, (i, j) ∉ E → y1 i j = 0 := fun i j hn =>
    h1.2.1 i j (fun hm => hn (Finset.mem_sdiff.1 hm).1)
  have z2E : ∀ i j, (i, j) ∉ E → y2 i j = 0 := fun i j hn =>
    h2.2.1 i j (fun hm => hn (Finset.mem_sdiff.1 hm).1)
  have z1 : ∀ i j, i ≠ j → i ≠ finRotate n j → y1 i j = 0 := fun i j hne hr =>
    z1E i j (fun hm => hr (fs_lc_off (hE hm) hne))
  have z2 : ∀ i j, i ≠ j → i ≠ finRotate n j → y2 i j = 0 := fun i j hne hr =>
    z2E i j (fun hm => hr (fs_lc_off (hE hm) hne))
  have y1a : y1 a.1 a.2 = 0 := h1.2.1 _ _ (by simp)
  have y2b : y2 b.1 b.2 = 0 := h2.2.1 _ _ (by simp)
  let g : Fin n → Fin n → ℝ := fun i j =>
    if i = j then min (y1 i j) (y2 i j) else max (y1 i j) (y2 i j)
  let h : Fin n → Fin n → ℝ := fun i j =>
    if i = j then max (y1 i j) (y2 i j) else min (y1 i j) (y2 i j)
  have hsum : ∑ i, ∑ j, y1 i j + ∑ i, ∑ j, y2 i j = ∑ i, ∑ j, g i j + ∑ i, ∑ j, h i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, h]
    split_ifs
    · linarith [min_add_max (y1 i j) (y2 i j)]
    · linarith [min_add_max (y1 i j) (y2 i j)]
  have hg : FlexFeasible C d E g := by
    refine ⟨fun i j => ?_, fun i j hn => ?_, fun j => ?_, fun i => ?_⟩
    · simp only [g]
      split_ifs
      · exact le_min (h1.1 i j) (h2.1 i j)
      · exact le_max_of_le_left (h1.1 i j)
    · simp [g, z1E i j hn, z2E i j hn]
    · refine fs_sum_le (fun i => g i j) (fun i => y1 i j) (fun i => y2 i j) C
        (h1.2.2.1 j) (h2.2.2.1 j) ?_
      rcases le_total (y1 (finRotate n j) j) (y2 (finRotate n j) j) with hle | hle
      · right
        intro i
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_right _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · subst hr; rw [max_eq_right hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
      · left
        intro i
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_left _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · subst hr; rw [max_eq_left hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
    · refine fs_sum_le (fun j => g i j) (fun j => y1 i j) (fun j => y2 i j) (d i)
        (h1.2.2.2 i) (h2.2.2.2 i) ?_
      set j0 := (finRotate n).symm i with hj0
      have hi0 : i = finRotate n j0 := by rw [hj0, Equiv.apply_symm_apply]
      rcases le_total (y1 i j0) (y2 i j0) with hle | hle
      · right
        intro j
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_right _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · have : j = j0 := by
              rw [hi0] at hr; exact ((finRotate n).injective hr).symm
            subst this; rw [max_eq_right hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
      · left
        intro j
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_left _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · have : j = j0 := by
              rw [hi0] at hr; exact ((finRotate n).injective hr).symm
            subst this; rw [max_eq_left hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
  have hh : FlexFeasible C d (E \ {a, b}) h := by
    refine ⟨fun i j => ?_, fun i j hn => ?_, fun j => ?_, fun i => ?_⟩
    · simp only [h]
      split_ifs
      · exact le_max_of_le_left (h1.1 i j)
      · exact le_min (h1.1 i j) (h2.1 i j)
    · by_cases hm : (i, j) ∈ E
      · have hab : (i, j) = a ∨ (i, j) = b := by
          by_contra hc
          push Not at hc
          exact hn (by simp [hm, hc.1, hc.2])
        rcases hab with hab | hab
        · have hne : i ≠ j := by
            intro he; apply hfa; rw [← hab]; exact he
          simp only [h, if_neg hne]
          have : y1 i j = 0 := by rw [← y1a, ← hab]
          rw [this]; exact min_eq_left (h2.1 i j)
        · have hne : i ≠ j := by
            intro he; apply hfb; rw [← hab]; exact he
          simp only [h, if_neg hne]
          have : y2 i j = 0 := by rw [← y2b, ← hab]
          rw [this]; exact min_eq_right (h1.1 i j)
      · simp [h, z1E i j hm, z2E i j hm]
    · refine fs_sum_le (fun i => h i j) (fun i => y1 i j) (fun i => y2 i j) C
        (h1.2.2.1 j) (h2.2.2.1 j) ?_
      rcases le_total (y1 j j) (y2 j j) with hle | hle
      · right
        intro i
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_right hle]
        · rw [if_neg hij]; exact min_le_right _ _
      · left
        intro i
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_left hle]
        · rw [if_neg hij]; exact min_le_left _ _
    · refine fs_sum_le (fun j => h i j) (fun j => y1 i j) (fun j => y2 i j) (d i)
        (h1.2.2.2 i) (h2.2.2.2 i) ?_
      rcases le_total (y1 i i) (y2 i i) with hle | hle
      · right
        intro j
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_right hle]
        · rw [if_neg hij]; exact min_le_right _ _
      · left
        intro j
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_left hle]
        · rw [if_neg hij]; exact min_le_left _ _
  rw [hsum]
  exact add_le_add (fs_le_perf C d E g hg) (fs_le_perf C d _ h hh)

open SupplyChainTheory in
lemma fs_pointwise {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (E : Finset (Fin n × Fin n)) (hE : E ⊆ longChain n) (a b : Fin n × Fin n)
    (ha : a ∈ E) (hb : b ∈ E) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b) :
    perf C d (E \ {a}) + perf C d (E \ {b}) ≤ perf C d E + perf C d (E \ {a, b}) := by
  have key := fs_key C d E hE a b hfa hfb
  unfold perf
  set X := sSup {v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j} +
    sSup {v | ∃ y, FlexFeasible C d (E \ {a, b}) y ∧ v = ∑ i, ∑ j, y i j} with hX
  have step : ∀ y1, FlexFeasible C d (E \ {a}) y1 →
      sSup {v | ∃ y, FlexFeasible C d (E \ {b}) y ∧ v = ∑ i, ∑ j, y i j}
        ≤ X - ∑ i, ∑ j, y1 i j := by
    intro y1 h1
    refine csSup_le (fs_nonempty C hC d hd _) ?_
    rintro v ⟨y2, h2, rfl⟩
    have := key y1 y2 h1 h2
    unfold perf at this
    linarith
  have : sSup {v | ∃ y, FlexFeasible C d (E \ {a}) y ∧ v = ∑ i, ∑ j, y i j}
      ≤ X - sSup {v | ∃ y, FlexFeasible C d (E \ {b}) y ∧ v = ∑ i, ∑ j, y i j} := by
    refine csSup_le (fs_nonempty C hC d hd _) ?_
    rintro v ⟨y1, h1, rfl⟩
    have := step y1 h1
    linarith
  linarith


open SupplyChainTheory in
lemma fs_mono {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 ≤ C) (d d' : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hle : ∀ i, d i ≤ d' i) (E : Finset (ι × ι)) :
    perf C d E ≤ perf C d' E := by
  refine csSup_le (fs_nonempty C hC d hd E) ?_
  rintro v ⟨y, hy, rfl⟩
  exact fs_le_perf C d' E y ⟨hy.1, hy.2.1, hy.2.2.1, fun i => (hy.2.2.2 i).trans (hle i)⟩

open SupplyChainTheory in
lemma fs_drop {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 ≤ C) (d d' : ι → ℝ)
    (hd' : ∀ i, 0 ≤ d' i) (hle : ∀ i, d' i ≤ d i) (E : Finset (ι × ι)) :
    perf C d E ≤ perf C d' E + ∑ i, (d i - d' i) := by
  refine csSup_le (fs_nonempty C hC d (fun i => (hd' i).trans (hle i)) E) ?_
  rintro v ⟨y, hy, rfl⟩
  let t : ι → ℝ := fun i => if ∑ j, y i j ≤ d' i then 1 else d' i / ∑ j, y i j
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i; simp only [t]; split_ifs with h
    · norm_num
    · exact div_nonneg (hd' i) ((hd' i).trans (not_le.1 h).le)
  have ht1 : ∀ i, t i ≤ 1 := by
    intro i; simp only [t]; split_ifs with h
    · exact le_rfl
    · have hp : 0 < ∑ j, y i j := lt_of_le_of_lt (hd' i) (not_le.1 h)
      rw [div_le_one hp]; exact (not_le.1 h).le
  have hrow : ∀ i, t i * ∑ j, y i j ≤ d' i ∧ ∑ j, y i j - t i * ∑ j, y i j ≤ d i - d' i := by
    intro i; simp only [t]; split_ifs with h
    · constructor
      · linarith
      · linarith [hle i]
    · have hp : 0 < ∑ j, y i j := lt_of_le_of_lt (hd' i) (not_le.1 h)
      rw [div_mul_cancel₀ _ hp.ne']
      exact ⟨le_rfl, by linarith [hy.2.2.2 i]⟩
  let y' : ι → ι → ℝ := fun i j => t i * y i j
  have hy' : FlexFeasible C d' E y' := by
    refine ⟨fun i j => mul_nonneg (ht0 i) (hy.1 i j), fun i j hn => by simp [y', hy.2.1 i j hn],
      fun j => ?_, fun i => ?_⟩
    · refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hy.2.2.1 j)
      exact mul_le_of_le_one_left (hy.1 i j) (ht1 i)
    · simp only [y']; rw [← Finset.mul_sum]; exact (hrow i).1
  have hv := fs_le_perf C d' E y' hy'
  have hsum : ∑ i, ∑ j, y i j ≤ ∑ i, ∑ j, y' i j + ∑ i, (d i - d' i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [y']; rw [← Finset.mul_sum]; linarith [(hrow i).2]
  linarith

open SupplyChainTheory in
lemma fs_lip {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 ≤ C) (E : Finset (ι × ι))
    (x z : ι → ℝ) :
    perf C (fun i => max (x i) 0) E ≤ perf C (fun i => max (z i) 0) E + ∑ i, |x i - z i| := by
  let m : ι → ℝ := fun i => min (max (x i) 0) (max (z i) 0)
  have h1 := fs_drop C hC (fun i => max (x i) 0) m
    (fun i => le_min (le_max_right _ _) (le_max_right _ _)) (fun i => min_le_left _ _) E
  have h2 := fs_mono C hC m (fun i => max (z i) 0)
    (fun i => le_min (le_max_right _ _) (le_max_right _ _)) (fun i => min_le_right _ _) E
  have h3 : ∑ i, (max (x i) 0 - m i) ≤ ∑ i, |x i - z i| := by
    refine Finset.sum_le_sum fun i _ => ?_
    have ha := abs_max_sub_max_le_abs (x i) (z i) 0
    have hb := le_abs_self (max (x i) 0 - max (z i) 0)
    simp only [m]
    rcases min_cases (max (x i) 0) (max (z i) 0) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      linarith [abs_nonneg (x i - z i)]
  linarith

open SupplyChainTheory in
lemma fs_cont {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (E : Finset (Fin n × Fin n)) :
    Continuous (fun x : Fin n → ℝ => perf C (fun i => max (x i) 0) E) := by
  refine (LipschitzWith.of_dist_le_mul (K := (n : NNReal)) fun x z => ?_).continuous
  have hs : ∑ i, |x i - z i| ≤ (n : ℝ) * dist x z := by
    have : ∀ i, |x i - z i| ≤ dist x z := fun i => by
      rw [← Real.dist_eq]; exact dist_le_pi_dist x z i
    calc ∑ i, |x i - z i| ≤ ∑ _i : Fin n, dist x z := Finset.sum_le_sum fun i _ => this i
      _ = (n : ℝ) * dist x z := by simp
  have hxz := fs_lip C hC E x z
  have hzx := fs_lip C hC E z x
  have hsym : ∑ i, |z i - x i| = ∑ i, |x i - z i| :=
    Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  rw [Real.dist_eq, NNReal.coe_natCast, abs_sub_le_iff]
  constructor <;> linarith

open SupplyChainTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n : ℕ}
    (S : BalancedSystem P n) (E : Finset (Fin n × Fin n)) (hE : E ⊆ longChain n)
    (a b : Fin n × Fin n) (ha : a ∈ E) (hb : b ∈ E) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b) :
    S.expPerf (E \ {a}) + S.expPerf (E \ {b}) ≤ S.expPerf E + S.expPerf (E \ {a, b}) := by
  have hDm : Measurable (fun ω => fun i => S.D i ω) := measurable_pi_lambda _ S.measurable_D
  have hint : ∀ E' : Finset (Fin n × Fin n),
      MeasureTheory.Integrable (fun ω => perf S.C (fun i => S.D i ω) E') P := by
    intro E'
    have hm : Measurable (fun ω => perf S.C (fun i => S.D i ω) E') := by
      have := (fs_cont S.C S.C_nonneg E').measurable.comp hDm
      convert this using 2 with ω
      simp only [Function.comp, max_eq_left (S.D_nonneg _ ω)]
    refine MeasureTheory.Integrable.mono' (g := fun ω => ∑ i, S.D i ω)
      (MeasureTheory.integrable_finsetSum _ fun i _ => S.integrable_D i)
      hm.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ perf S.C (fun i => S.D i ω) E' := by
      have := fs_le_perf S.C (fun i => S.D i ω) E' (fun _ _ => 0)
        ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ => by simp [S.C_nonneg],
          fun i => by simp [S.D_nonneg i ω]⟩
      simpa using this
    have hup : perf S.C (fun i => S.D i ω) E' ≤ ∑ i, S.D i ω :=
      csSup_le (fs_nonempty S.C S.C_nonneg _ (fun i => S.D_nonneg i ω) E')
        (by rintro v ⟨y, hy, rfl⟩; exact Finset.sum_le_sum fun i _ => hy.2.2.2 i)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hup
  unfold BalancedSystem.expPerf
  rw [← MeasureTheory.integral_add (hint _) (hint _), ← MeasureTheory.integral_add (hint _) (hint _)]
  exact MeasureTheory.integral_mono ((hint _).add (hint _)) ((hint _).add (hint _))
    fun ω => fs_pointwise S.C S.C_nonneg (fun i => S.D i ω) (fun i => S.D_nonneg i ω) E hE a b
      ha hb hfa hfb
