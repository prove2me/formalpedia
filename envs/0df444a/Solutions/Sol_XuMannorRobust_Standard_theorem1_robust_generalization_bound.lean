-- Prove2me | solution 1 for XuMannorRobust.Standard.theorem1_robust_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:34:30.460181+00:00
-- url     : https://prove2.me/submissions/9e97ffe3-75d2-4c63-9dd4-b392072fee0b

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Standard_IsRobust
import Definitions.Def_XuMannorRobust_Standard_CellCount
open MeasureTheory ProbabilityTheory XuMannorRobust.Standard
open scoped BigOperators
noncomputable section

private theorem bounded_average_tail {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : Measurable f)
    (hb : ∀ z, f z ∈ Set.Icc (-1) 1) {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi (fun _ : Fin n => μ)) {s | lam ≤ (∑ j, f (s j)) / (n : ℝ) - ∫ z, f z ∂μ} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ)*lam^2)/2)) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  let X (j : Fin n) (s : Fin n → Z) := f (s j) - ∫ z, f z ∂μ
  have hind : iIndepFun X P := iIndepFun_pi (fun _ => (hf.sub_const _).aemeasurable)
  have hsub (j : Fin n) : HasSubgaussianMGF (X j) 1 P := by
    have hh := hasSubgaussianMGF_of_mem_Icc (μ := P)
      (X := fun s : Fin n → Z => f (s j)) (hf.comp (measurable_pi_apply j)).aemeasurable
      (Filter.Eventually.of_forall fun s => hb (s j))
    rw [integral_comp_eval (μ := fun _ : Fin n => μ) hf.aestronglyMeasurable] at hh
    norm_num at hh
    exact hh
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => (1 : NNReal)) (fun j _ => hsub j)
    (show 0 ≤ (n : ℝ)*lam from mul_nonneg hn'.le hlam)
  have heq : {s : Fin n → Z | lam ≤ (∑ j, f (s j))/(n : ℝ) - ∫ z, f z ∂μ} =
      {s | (n : ℝ)*lam ≤ ∑ j, X j s} := by
    ext s
    simp only [Set.mem_setOf_eq, X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hc : (∑ j, f (s j))/(n : ℝ)*(n : ℝ) = ∑ j, f (s j) := div_mul_cancel₀ _ hn'.ne'
    constructor <;> intro h <;> nlinarith
  rw [heq]
  rw [← ofReal_measureReal (μ := P)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, NNReal.coe_natCast] at hh
  have he : -((n : ℝ)*lam)^2/(2*(n : ℝ)) = -((n : ℝ)*lam^2)/2 := by field_simp
  simpa only [he] using hh

private theorem bhc {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi fun _ : Fin n => μ)
        {s | lam ≤ ∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal|}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ K * Real.exp (-((n : ℝ) * lam ^ 2) / 2)) := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let sign (σ : Fin K → Bool) (i : Fin K) : ℝ := if σ i then 1 else -1
  let g (σ : Fin K → Bool) (z : Z) := ∑ i, (C i).indicator (fun _ => sign σ i) z
  have hg (σ : Fin K → Bool) : Measurable (g σ) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator (hC_meas i)
  have hgi (σ : Fin K → Bool) (z : Z) (i : Fin K) (hi : z ∈ C i) : g σ z = sign σ i := by
    dsimp only [g]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      have hj : z ∉ C j := fun hj => Set.disjoint_left.mp (hC_disj hji) hj hi
      exact Set.indicator_of_notMem hj _
    · simp
  have hgb (σ : Fin K → Bool) (z : Z) : g σ z ∈ Set.Icc (-1) 1 := by
    obtain ⟨i, hi⟩ : ∃ i, z ∈ C i := by
      apply Set.mem_iUnion.mp
      rw [hC_cover]
      trivial
    rw [hgi σ z i hi]
    dsimp [sign]
    split <;> norm_num
  have hmean (σ : Fin K → Bool) : ∫ z, g σ z ∂μ = ∑ i, μ.real (C i) * sign σ i := by
    rw [show g σ = fun z => ∑ i, (C i).indicator (fun _ => sign σ i) z from rfl, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      simpa using integral_indicator_const (μ := μ) (sign σ i) (hC_meas i)
    · intro i _
      exact (integrable_const _).indicator (hC_meas i)
  have hsample (σ : Fin K → Bool) (s : Fin n → Z) :
      (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ =
      ∑ i, sign σ i * ((cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i)) := by
    dsimp only [g]
    rw [Finset.sum_comm]
    have hh (i : Fin K) : (∑ j, (C i).indicator (fun _ => sign σ i) (s j)) =
        (cellCount C s i : ℝ) * sign σ i := by
      simp only [Set.indicator_apply, ← Finset.sum_filter]
      simp [cellCount]
    simp_rw [hh]
    change (∑ i, (cellCount C s i : ℝ)*sign σ i)/(n : ℝ) - ∫ z, g σ z ∂μ = _
    rw [hmean, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let E (σ : Fin K → Bool) := {s : Fin n → Z | lam ≤ (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ}
  have hsub : {s : Fin n → Z | lam ≤ ∑ i, |(cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal|} ⊆ ⋃ σ, E σ := by
    intro s hs
    let σ (i : Fin K) : Bool := decide (0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i))
    apply Set.mem_iUnion.mpr
    refine ⟨σ, ?_⟩
    change lam ≤ (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ
    rw [hsample]
    change lam ≤ ∑ i, |(cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal| at hs
    convert hs using 1
    congr 1
    funext i
    dsimp only [sign, σ]
    split <;> rename_i hi
    · have hh : 0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i) := of_decide_eq_true hi
      change 0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal at hh
      rw [one_mul, abs_of_nonneg hh]
      rfl
    · have hh : ¬0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i) := fun h => hi (by simp [h])
      change ¬0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal at hh
      rw [neg_one_mul, abs_of_neg (lt_of_not_ge hh)]
      rfl
  calc
    _ ≤ P (⋃ σ, E σ) := measure_mono hsub
    _ ≤ ∑' σ, P (E σ) := measure_iUnion_le _
    _ = ∑ σ, P (E σ) := tsum_fintype _
    _ ≤ ∑ σ : Fin K → Bool, ENNReal.ofReal (Real.exp (-((n : ℝ)*lam^2)/2)) := by
      apply Finset.sum_le_sum
      intro σ _
      exact bounded_average_tail μ (g σ) (hg σ) (hgb σ) hn lam hlam
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp [Fintype.card_fun, Fintype.card_fin]
      · intro σ _
        exact (Real.exp_pos _).le

private theorem cell_deviation_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s | ¬ (∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal|
            ≤ Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by
  by_cases hd : 1 ≤ δ
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal hd)
  have hd1 : δ < 1 := lt_of_not_ge hd
  let x := (2*(K : ℝ)*Real.log 2 + 2*Real.log (1/δ))/(n : ℝ)
  have hx : 0 ≤ x := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hld : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
    positivity
  have hb := bhc μ C hC_meas hC_disj hC_cover hn (Real.sqrt x) (Real.sqrt_nonneg x)
  have hsub : {s : Fin n → Z | ¬(∑ i, |(cellCount C s i : ℝ)/(n : ℝ)-(μ (C i)).toReal| ≤ Real.sqrt x)} ⊆
      {s | Real.sqrt x ≤ ∑ i, |(cellCount C s i : ℝ)/(n : ℝ)-(μ (C i)).toReal|} :=
    fun s hs => (lt_of_not_ge hs).le
  apply (measure_mono hsub).trans
  have he : (2 : ℝ)^K * Real.exp (-((n : ℝ)*(Real.sqrt x)^2)/2) = δ := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    have heq : -((n : ℝ)*(Real.sqrt x)^2)/2 = -((K : ℝ)*Real.log 2) + Real.log δ := by
      rw [Real.sq_sqrt hx]
      dsimp [x]
      rw [Real.log_div (by norm_num) hδ.ne', Real.log_one]
      field_simp
      ring
    rw [heq, Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log hδ]
    field_simp
  rwa [he] at hb

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

private theorem deterministic_gap {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
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

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ) (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) (K : ℕ)
    (ε : (Fin n → Z) → ℝ) (hA : IsRobust l A K ε) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s | ¬ (|expectedLoss μ l (A s) - empiricalLoss l (A s) s|
            ≤ ε s + M * Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by
  obtain ⟨C, hCm, hCd, hCc, hCr⟩ := hA
  apply le_trans (measure_mono ?_) (cell_deviation_bound μ C hCm hCd hCc hn δ hδ)
  intro s hs hgood
  apply hs
  have hgap := deterministic_gap μ l M hl_bound hl_meas hn A ε C hCm hCd hCc hCr s
  have hM : 0 ≤ M := (hl_bound (A s) (s ⟨0, hn⟩)).1.trans (hl_bound (A s) (s ⟨0, hn⟩)).2
  have hh := mul_le_mul_of_nonneg_left hgood hM
  linarith
