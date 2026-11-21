-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:28:59.235414+00:00
-- url     : https://prove2.me/submissions/99c68083-0ed0-4437-a38b-4559de74918f

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
import Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_3_1
import Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_3_2

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T3
open OptimalAgnosticPAC.Learner

theorem loss_eq (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (y : Bool) :
    loss a y = (1 - sgn y * a) / 2 := by
  obtain ⟨h1, h2⟩ := ha
  unfold loss sgn
  cases y
  · simp only [Bool.false_eq_true, if_false]
    rw [abs_of_nonneg (by linarith)]; ring
  · simp only [if_true]
    rw [abs_of_nonpos (by linarith)]; ring

theorem measurable_loss {X : Type} [MeasurableSpace X] (g : X → ℝ) (hg : Measurable g) :
    Measurable (fun z : X × Bool => loss (g z.1) z.2) := by
  unfold loss
  have h1 : Measurable (fun z : X × Bool => sgn z.2) :=
    (measurable_from_top (f := sgn)).comp measurable_snd
  exact ((((hg.comp measurable_fst).sub h1).abs).div_const 2)

theorem scoreRisk_avg {X : Type} [MeasurableSpace X] (P : Measure (X × Bool))
    [IsProbabilityMeasure P] {k : ℕ} (hk : 1 ≤ k) (g : Fin k → X → ℝ)
    (hm : ∀ j, Measurable (g j)) (hr : ∀ j x, g j x ∈ Set.Icc (-1 : ℝ) 1) :
    scoreRisk P (fun x => (1 / (k : ℝ)) * ∑ j, g j x) =
      (1 / (k : ℝ)) * ∑ j, scoreRisk P (g j) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hint : ∀ j, Integrable (fun z : X × Bool => loss (g j z.1) z.2) P := by
    intro j
    refine Integrable.of_bound (measurable_loss _ (hm j)).aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro z
    rw [Real.norm_eq_abs, loss_eq _ (hr j z.1)]
    have := hr j z.1
    unfold sgn
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [this.1, this.2]
  have havg : ∀ x, (1 / (k : ℝ)) * ∑ j, g j x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    have h1 : ∑ j, g j x ≤ k := by
      calc ∑ j, g j x ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun j _ => (hr j x).2)
        _ = k := by simp
    have h2 : -(k : ℝ) ≤ ∑ j, g j x := by
      calc -(k : ℝ) = ∑ _j : Fin k, (-1 : ℝ) := by simp
        _ ≤ ∑ j, g j x := Finset.sum_le_sum (fun j _ => (hr j x).1)
    constructor
    · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hkR]; linarith
    · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hkR]; linarith
  unfold scoreRisk
  have : ∀ z : X × Bool, loss ((1 / (k : ℝ)) * ∑ j, g j z.1) z.2 =
      (1 / (k : ℝ)) * ∑ j, loss (g j z.1) z.2 := by
    intro z
    rw [loss_eq _ (havg z.1) z.2]
    rw [Finset.sum_congr rfl (fun j _ => loss_eq _ (hr j z.1) z.2)]
    rw [← Finset.sum_div]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    field_simp
  simp_rw [this]
  rw [integral_const_mul, integral_finset_sum _ (fun j _ => hint j)]

theorem marg {α : Type} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (N M : ℕ) (h : N + 1 = M) (A : Set (Fin N → α)) :
    Measure.pi (fun _ : Fin N => P) A ≤
      Measure.pi (fun _ : Fin M => P) ((fun (S : Fin M → α) (i : Fin N) => S (Fin.castLE (by omega) i)) ⁻¹' A) := by
  subst h
  set μ1 : Measure (Fin N → α) := Measure.pi (fun _ : Fin N => P) with hμ1
  set μ2 : Measure (Fin (N + 1) → α) := Measure.pi (fun _ : Fin (N + 1) => P) with hμ2
  set g : (Fin (N + 1) → α) → (Fin N → α) := fun S i => S (Fin.castLE (by omega) i) with hg
  obtain ⟨C, hCsub, hCmeas, hCeq⟩ := exists_measurable_superset μ2 (g ⁻¹' A)
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => P) (Fin.last N)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) (Fin.last N) with he
  set B : Set (α × (Fin N → α)) := e.symm ⁻¹' C with hB
  have hBmeas : MeasurableSet B := e.symm.measurable hCmeas
  have h1 : μ2 C = (P.prod μ1) B := by
    have := hmp.measure_preimage_equiv B
    have hh : e ⁻¹' B = C := by
      ext S; simp [hB]
    rw [hh] at this
    simpa [hμ1, hμ2] using this
  rw [← hCeq]
  refine le_trans ?_ (le_of_eq h1.symm)
  rw [Measure.prod_apply_symm hBmeas]
  have hmeasf : Measurable (fun y : Fin N → α => P ((fun x => (x, y)) ⁻¹' B)) :=
    measurable_measure_prodMk_right hBmeas
  let A'' : Set (Fin N → α) := {y | P ((fun x => (x, y)) ⁻¹' B) = 1}
  have hA'' : MeasurableSet A'' := hmeasf (measurableSet_singleton 1)
  have hAsub : A ⊆ A'' := by
    intro s hs
    have : (fun x => (x, s)) ⁻¹' B = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ, iff_true, hB]
      apply hCsub
      simp only [Set.mem_preimage, hg]
      have : (fun i : Fin N => (e.symm (x, s)) (Fin.castLE (by omega) i)) = s := by
        funext i
        have : Fin.castLE (by omega : N ≤ N + 1) i = (Fin.last N).succAbove i := by
          ext; simp [Fin.succAbove_last]
        rw [this]
        simp [he, MeasurableEquiv.piFinSuccAbove]
      rw [this]; exact hs
    show P _ = 1
    rw [this]; exact measure_univ
  calc μ1 A ≤ μ1 A'' := measure_mono hAsub
    _ = ∫⁻ y, A''.indicator 1 y ∂μ1 := by rw [lintegral_indicator_one hA'']
    _ ≤ _ := by
      refine lintegral_mono (fun y => ?_)
      by_cases hy : y ∈ A''
      · simp only [Set.indicator_of_mem hy, Pi.one_apply]; exact le_of_eq hy.symm
      · simp only [Set.indicator_of_notMem hy]; exact zero_le
end OptimalAgnosticPAC.Dev.T3
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T3
open OptimalAgnosticPAC.Learner

theorem avg_mem {k : ℕ} (hk : 1 ≤ k) (a : Fin k → ℝ) (h : ∀ j, a j ∈ Set.Icc (-1 : ℝ) 1) :
    (1 / (k : ℝ)) * ∑ j, a j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : ∑ j, a j ≤ k := by
    calc ∑ j, a j ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun j _ => (h j).2)
      _ = k := by simp
  have h2 : -(k : ℝ) ≤ ∑ j, a j := by
    calc -(k : ℝ) = ∑ _j : Fin k, (-1 : ℝ) := by simp
      _ ≤ ∑ j, a j := Finset.sum_le_sum (fun j _ => (h j).1)
  constructor
  · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hkR]; linarith
  · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hkR]; linarith

theorem bridge {k : ℕ} (G : Fin (2 * k) → ℝ) :
    ∑ j : Fin k, G ⟨k + j, by omega⟩ = ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val), G t := by
  refine Finset.sum_bij' (fun j _ => ⟨k + j, by omega⟩) (fun t ht => ⟨t.val - k, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro j _; simp
  · intro t ht; simp
  · intro j _; ext; simp
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    ext; simp; omega
  · intro j _; rfl
end OptimalAgnosticPAC.Dev.T3

namespace OptimalAgnosticPAC.Learner
open OptimalAgnosticPAC.Dev.T3

theorem chk_theorem_3 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (hmin : AttainsMinRisk P H)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ (S : Fin (2 * k - 1) → X × Bool) (x : X), suffixAvg q k S x ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      sampleLaw P (2 * k - 1)
        {S | minRisk P H +
              17000 * (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (3 / δ)) / (k : ℝ)) +
                ((d : ℝ) + Real.log (3 / δ)) / (k : ℝ)) <
            scoreRisk P (suffixAvg q k S)} ≤
        ENNReal.ofReal δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun S x => avg_mem hk _ (fun j => hq.mem_Icc _ _ _), ?_⟩
  intro δ hδ0 hδ1
  obtain ⟨hs, hhs, hrisk⟩ := hmin
  have hδ'0 : 0 < δ / 3 := by positivity
  have hδ'1 : δ / 3 ≤ 1 / 3 := by linarith
  have h31 := lemma_3_1 H d hd hVC hmeas q hq P k hk hs hhs (δ / 3) hδ'0 hδ'1
  have h32 := lemma_3_2 H d hd hVC hmeas q hq P k hk hs hhs (δ / 3) hδ'0 hδ'1
  have hl : Real.log (1 / (δ / 3)) = Real.log (3 / δ) := by congr 1; field_simp
  rw [hl] at h31 h32
  have hlog : 0 ≤ Real.log (3 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hL0 : 0 ≤ risk P hs := by unfold risk; exact measureReal_nonneg
  refine le_trans (marg P (2 * k - 1) (2 * k) (by omega) _) ?_
  have hunion := le_trans (measure_union_le _ _) (add_le_add h31 h32)
  refine le_trans (measure_mono ?_) (hunion.trans ?_)
  swap
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply le_of_eq; congr 1; ring
  intro S' hS'
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hS'
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨n1, n2⟩ := hcon
  simp only [Set.mem_setOf_eq, not_lt] at n1 n2
  set M := max (excessLossSum q hs k S') 0 with hM
  set ℓ := Real.log (3 / δ) with hℓ
  set Lm := risk P hs with hLm
  -- the average of scores
  have hmeasq : ∀ (m : ℕ) (T : Fin m → X × Bool), Measurable (fun x => q m T x) :=
    fun m T => (hq.measurable m).comp (measurable_const.prodMk measurable_id)
  have hSR : scoreRisk P (suffixAvg q k (fun i : Fin (2 * k - 1) => S' (Fin.castLE (by omega) i))) =
      (1 / (k : ℝ)) * ∑ j : Fin k, scoreRisk P (q (k + j) (prefixSample S' (k + j) (by omega))) := by
    unfold suffixAvg
    exact scoreRisk_avg P hk _ (fun j => hmeasq _ _) (fun j x => hq.mem_Icc _ _ _)
  have hbr := bridge (k := k) (fun t => scoreRisk P (q t (prefixSample S' t t.isLt.le)) - Lm)
  have hbr' : ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
      (scoreRisk P (q t (prefixSample S' t t.isLt.le)) - Lm) =
      ∑ j : Fin k, scoreRisk P (q (k + j) (prefixSample S' (k + j) (by omega))) - k * Lm := by
    rw [← hbr, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hA : 0 ≤ Real.sqrt (Lm * ((d : ℝ) + ℓ) / k) := Real.sqrt_nonneg _
  have hB : Real.sqrt (Lm * ℓ / k) ≤ Real.sqrt (Lm * ((d : ℝ) + ℓ) / k) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hkR.le
    nlinarith [(by positivity : (0 : ℝ) ≤ d)]
  have hC : ℓ / k ≤ ((d : ℝ) + ℓ) / k :=
    div_le_div_of_nonneg_right (by linarith [(by positivity : (0 : ℝ) ≤ d)]) hkR.le
  rw [hSR] at hS'
  rw [← hrisk] at hS'
  rw [hbr'] at n2
  have e2 : 2 / (k : ℝ) * M = 2 * (1 / (k : ℝ) * M) := by ring
  rw [e2] at n2
  have key : (1 / (k : ℝ)) * (∑ j : Fin k, scoreRisk P (q (k + j) (prefixSample S' (k + j) (by omega))) - k * Lm)
      = (1 / (k : ℝ)) * ∑ j : Fin k, scoreRisk P (q (k + j) (prefixSample S' (k + j) (by omega))) - Lm := by
    field_simp
  rw [key] at n2
  have hCnn : 0 ≤ ((d : ℝ) + ℓ) / k := by positivity
  linarith [hA, hB, hC, hCnn, n1, n2, hS']
end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_theorem_3 := @OptimalAgnosticPAC.Learner.chk_theorem_3
