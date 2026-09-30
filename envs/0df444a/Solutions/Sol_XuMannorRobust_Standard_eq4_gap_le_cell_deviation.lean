-- Prove2me | solution 1 for XuMannorRobust.Standard.eq4_gap_le_cell_deviation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:25:24.159986+00:00
-- url     : https://prove2.me/submissions/9ef673a1-53a1-4a76-8533-27bcf83662ff

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Standard_CellCount
open MeasureTheory XuMannorRobust.Standard
open scoped BigOperators
noncomputable section

private theorem finite_mean {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (f : ι → ℝ)
    (M : ℝ) (hf : ∀ i ∈ N, 0 ≤ f i ∧ f i ≤ M) :
    0 ≤ (∑ i ∈ N, f i) / N.card ∧ (∑ i ∈ N, f i) / N.card ≤ M := by
  have hc : (0 : ℝ) < N.card := Nat.cast_pos.mpr hN.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i hi => (hf i hi).1) hc.le
  · apply (div_le_iff₀ hc).2
    have hh := Finset.sum_le_sum (fun i hi => (hf i hi).2)
    simpa [mul_comm] using hh

private theorem finite_mean_close {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (f : ι → ℝ)
    (v ε : ℝ) (hf : ∀ i ∈ N, |f i - v| ≤ ε) :
    |v - (∑ i ∈ N, f i) / N.card| ≤ ε := by
  have hc : (0 : ℝ) < N.card := Nat.cast_pos.mpr hN.card_pos
  have hupper := Finset.sum_le_sum (fun i hi => (abs_le.mp (hf i hi)).2)
  have hlower := Finset.sum_le_sum (fun i hi => (abs_le.mp (hf i hi)).1)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hupper hlower
  have hdiv : (∑ i ∈ N, f i) / (N.card : ℝ) * N.card = ∑ i ∈ N, f i := div_mul_cancel₀ _ hc.ne'
  apply abs_le.mpr
  constructor <;> nlinarith

private theorem cell_bound {Z ι : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hf : Integrable f μ) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (C : Set Z) (hC : MeasurableSet C) (N : Finset ι) (s : ι → Z)
    (hr : ∀ i ∈ N, ∀ z ∈ C, |f (s i) - f z| ≤ ε)
    (n : ℝ) (hn : 0 < n) :
    |(∫ z in C, f z ∂μ) - (∑ i ∈ N, f (s i)) / n| ≤
      ε * μ.real C + M * |(N.card : ℝ) / n - μ.real C| := by
  classical
  let p := μ.real C
  let B := ∫ z in C, f z ∂μ
  have hp : 0 ≤ p := measureReal_nonneg
  have hB0 : 0 ≤ B := integral_nonneg fun z => (hb z).1
  have hBM : B ≤ p * M := by
    have hh := integral_mono (hf.integrableOn : Integrable f (μ.restrict C)) (integrable_const M) (fun z => (hb z).2)
    simpa [B, p, setIntegral_const] using hh
  by_cases hN : N.Nonempty
  · let m := (∑ i ∈ N, f (s i)) / (N.card : ℝ)
    have hm := finite_mean N hN (fun i => f (s i)) M (fun i _ => hb (s i))
    change 0 ≤ m ∧ m ≤ M at hm
    have hclose : ∀ z ∈ C, |f z - m| ≤ ε := by
      intro z hz
      exact finite_mean_close N hN (fun i => f (s i)) (f z) ε (fun i hi => hr i hi z hz)
    have hlow : p * (m - ε) ≤ B := by
      have hh := integral_mono_ae (integrable_const (m-ε)) hf.integrableOn
        ((ae_restrict_iff' hC).2 (Filter.Eventually.of_forall fun z hz => by
          have h := (abs_le.mp (hclose z hz)).1
          linarith))
      simpa [B, p, setIntegral_const] using hh
    have hupp : B ≤ p * (m + ε) := by
      have hh := integral_mono_ae hf.integrableOn (integrable_const (m+ε))
        ((ae_restrict_iff' hC).2 (Filter.Eventually.of_forall fun z hz => by
          have h := (abs_le.mp (hclose z hz)).2
          linarith))
      simpa [B, p, setIntegral_const] using hh
    have hdiff : |B - p*m| ≤ ε*p := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have hc : (N.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN.card_pos)
    have heq : (∑ i ∈ N, f (s i)) / n = (N.card : ℝ) / n * m := by dsimp [m]; field_simp
    rw [heq]
    change |B - (N.card : ℝ) / n * m| ≤ _
    calc
      _ ≤ |B - p*m| + |p*m - (N.card : ℝ)/n*m| := abs_sub_le _ _ _
      _ = |B - p*m| + |(N.card : ℝ)/n - p| * m := by
        rw [← sub_mul, abs_mul, abs_of_nonneg hm.1, abs_sub_comm p]
      _ ≤ ε*p + M * |(N.card : ℝ)/n - p| := by
        have hh := mul_le_mul_of_nonneg_left hm.2 (abs_nonneg ((N.card : ℝ)/n-p))
        nlinarith
  · have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    simp only [he, Finset.sum_empty, zero_div, sub_zero, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg hB0, abs_of_nonneg hp]
    nlinarith

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ) (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) {K : ℕ}
    (ε : (Fin n → Z) → ℝ) (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    (hC_robust : ∀ s : Fin n → Z, ∀ j : Fin n, ∀ z : Z, ∀ i : Fin K,
      s j ∈ C i → z ∈ C i → |l (A s) (s j) - l (A s) z| ≤ ε s) :
    ∀ s : Fin n → Z,
      |expectedLoss μ l (A s) - empiricalLoss l (A s) s|
        ≤ ε s + M * ∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal| := by
  classical
  intro s
  let f := l (A s)
  let N (i : Fin K) := Finset.univ.filter (fun j => s j ∈ C i)
  have hf : Integrable f μ := by
    apply (integrable_const M).mono' (hl_meas (A s)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hl_bound (A s) z).1] using (hl_bound (A s) z).2
  have hcover (z : Z) : ∃ i, z ∈ C i := by
    have hz : z ∈ ⋃ i, C i := by rw [hC_cover]; trivial
    exact Set.mem_iUnion.mp hz
  have hM : 0 ≤ M := (hl_bound (A s) (s ⟨0, hn⟩)).1.trans (hl_bound (A s) (s ⟨0, hn⟩)).2
  have he : 0 ≤ ε s := by
    obtain ⟨i, hi⟩ := hcover (s ⟨0, hn⟩)
    simpa using hC_robust s ⟨0, hn⟩ (s ⟨0, hn⟩) i hi hi
  have hsum (g : Fin n → ℝ) : ∑ i, ∑ j ∈ N i, g j = ∑ j, g j := by
    simp only [N, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨i, hi⟩ := hcover (s j)
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro k _ hki
      have hk : s j ∉ C k := fun hk => Set.disjoint_left.mp (hC_disj hki) hk hi
      simp [hk]
    · simp
  have hpop : expectedLoss μ l (A s) = ∑ i, ∫ z in C i, f z ∂μ := by
    have hh := integral_iUnion_fintype hC_meas hC_disj (fun i => hf.integrableOn)
    simpa only [hC_cover, setIntegral_univ, expectedLoss, f] using hh
  have hemp : empiricalLoss l (A s) s = ∑ i, (∑ j ∈ N i, f (s j)) / (n : ℝ) := by
    rw [← Finset.sum_div, hsum]
    simp [empiricalLoss, div_eq_mul_inv, mul_comm, f]
  have hp : ∑ i, μ.real (C i) = 1 := by
    have hh := integral_iUnion_fintype (f := fun _ : Z => (1 : ℝ)) hC_meas hC_disj
      (fun i => (integrable_const (μ := μ) (1 : ℝ)).integrableOn)
    simpa [hC_cover, setIntegral_const] using hh.symm
  have hcell (i : Fin K) :
      |(∫ z in C i, f z ∂μ) - (∑ j ∈ N i, f (s j)) / (n : ℝ)| ≤
      ε s * μ.real (C i) + M * |(cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i)| := by
    apply cell_bound μ f M (ε s) hM he hf (hl_bound (A s)) (C i) (hC_meas i) (N i) s ?_ (n : ℝ) (Nat.cast_pos.mpr hn)
    intro j hj z hz
    exact hC_robust s j z i (by simpa [N] using hj) hz
  rw [hpop, hemp, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∫ z in C i, f z ∂μ) - (∑ j ∈ N i, f (s j))/(n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (ε s * μ.real (C i) + M * |(cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i)|) :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]; simp [measureReal_def]
