-- Prove2me | solution 1 for VarianceRegularization.Covering.robust_minimizer_oracle_inequality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:01:22.703676+00:00
-- url     : https://prove2.me/submissions/bfc53bc7-26f6-4861-a0dc-f6622e0009ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup
import Definitions.Def_VarianceRegularization_Covering_empCoveringNumber
import Theorems.Thm_VarianceRegularization_Covering_uniform_empirical_bernstein
import Theorems.Thm_VarianceRegularization_Covering_fixed_function_bernstein
import Theorems.Thm_VarianceRegularization_Covering_sample_std_upper_tail
import Theorems.Thm_VarianceRegularization_Covering_two_sided_variance_bound

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Covering
namespace RMOI

lemma sampleVar_le_shift {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (m : ℝ) :
    sampleVar z ≤ (n : ℝ)⁻¹ * ∑ i, (z i - m) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e : ∑ i, (z i - m) ^ 2 = ∑ i, z i ^ 2 - 2 * m * ∑ i, z i + n * m ^ 2 := by
    calc ∑ i, (z i - m) ^ 2 = ∑ i, (z i ^ 2 - 2 * m * z i + m ^ 2) :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp
  unfold sampleVar VarianceRegularization.Expansion.empMean
  rw [e]
  have key : (n : ℝ)⁻¹ * (∑ i, z i ^ 2 - 2 * m * ∑ i, z i + n * m ^ 2)
      - ((n : ℝ)⁻¹ * ∑ i, z i ^ 2 - ((n : ℝ)⁻¹ * ∑ i, z i) ^ 2)
      = ((n : ℝ)⁻¹ * ∑ i, z i - m) ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg ((n : ℝ)⁻¹ * ∑ i, z i - m)]

lemma sampleVar_const {n : ℕ} (hn : 0 < n) (c : ℝ) : sampleVar (fun _ : Fin n => c) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold sampleVar VarianceRegularization.Expansion.empMean
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma continuous_sampleVar (n : ℕ) : Continuous (fun z : Fin n → ℝ => sampleVar z) := by
  unfold sampleVar VarianceRegularization.Expansion.empMean
  fun_prop

lemma integral_sampleVar_le {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (M0 M1 : ℝ) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) :
    ∫ W, sampleVar W ∂(Measure.pi (fun _ : Fin n => P.map f)) ≤ variance f P := by
  have hpi : (Measure.pi (fun _ : Fin n => P)).map (fun s i => f (s i))
      = Measure.pi (fun _ : Fin n => P.map f) :=
    Measure.pi_map_pi (fun _ => hf.aemeasurable)
  have hφ : Measurable (fun (s : Fin n → X) (i : Fin n) => f (s i)) := by fun_prop
  rw [← hpi, integral_map hφ.aemeasurable (continuous_sampleVar n).aestronglyMeasurable]
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ x, f x ∂P := ⟨_, rfl⟩
  have hfm2 : Measurable (fun x => (f x - m) ^ 2) := (hf.sub_const m).pow_const 2
  have hbd : ∀ x, ‖(f x - m) ^ 2‖ ≤ (|M0| + |M1| + |m|) ^ 2 := by
    intro x
    have h1 := (hfb x).1
    have h2 := (hfb x).2
    rw [Real.norm_eq_abs, abs_pow]
    have : |f x - m| ≤ |M0| + |M1| + |m| := by
      rw [abs_le]; constructor <;>
        nlinarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg m, le_abs_self M0, neg_abs_le M0,
          le_abs_self M1, neg_abs_le M1, le_abs_self m, neg_abs_le m]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hint1 : Integrable (fun x => (f x - m) ^ 2) P :=
    Integrable.of_bound hfm2.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)
  have hint : ∀ i : Fin n, Integrable (fun s : Fin n → X => (f (s i) - m) ^ 2)
      (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    exact Integrable.of_bound (hfm2.comp (measurable_pi_apply i)).aestronglyMeasurable _ (Filter.Eventually.of_forall (fun s => hbd (s i)))
  have hH : Integrable (fun s : Fin n → X => (n : ℝ)⁻¹ * ∑ i, (f (s i) - m) ^ 2)
      (Measure.pi (fun _ : Fin n => P)) :=
    (integrable_finsetSum _ (fun i _ => hint i)).const_mul _
  have hval : ∫ s, (n : ℝ)⁻¹ * ∑ i, (f (s i) - m) ^ 2 ∂(Measure.pi (fun _ : Fin n => P))
      = variance f P := by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
    have : ∀ i : Fin n, ∫ s, (f (s i) - m) ^ 2 ∂(Measure.pi (fun _ : Fin n => P))
        = ∫ x, (f x - m) ^ 2 ∂P := fun i =>
      integral_comp_eval (μ := fun _ : Fin n => P) (f := fun x => (f x - m) ^ 2)
        hint1.aestronglyMeasurable
    rw [variance_eq_integral hf.aemeasurable, ← hm]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [← hval]
  by_cases hI : Integrable (fun s : Fin n → X => sampleVar (fun i => f (s i)))
      (Measure.pi (fun _ : Fin n => P))
  · exact integral_mono hI hH (fun s => sampleVar_le_shift hn _ m)
  · rw [integral_undef hI]
    exact integral_nonneg (fun s => by positivity)

/-- Inline: the sample standard deviation tail for one bounded function. -/
lemma sample_std_tail_fn {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (M0 M1 : ℝ) (hM : M0 ≤ M1) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => P)
        {s | Real.sqrt (variance f P) + (M1 - M0) * Real.sqrt (2 * t / n)
          < Real.sqrt (sampleVar (fun i => f (s i)))}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  rcases hM.lt_or_eq with hlt | heq
  · have : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
    have hpi : (Measure.pi (fun _ : Fin n => P)).map (fun s i => f (s i))
        = Measure.pi (fun _ : Fin n => P.map f) :=
      Measure.pi_map_pi (fun _ => hf.aemeasurable)
    have hφ : Measurable (fun (s : Fin n → X) (i : Fin n) => f (s i)) := by fun_prop
    have hP : ∀ᵐ z ∂(P.map f), z ∈ Set.Icc M0 M1 :=
      (ae_map_iff hf.aemeasurable measurableSet_Icc).mpr (Filter.Eventually.of_forall hfb)
    set τ := (M1 - M0) * Real.sqrt (2 * t / n) with hτ
    have hτ0 : 0 ≤ τ := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have key := integral_sampleVar_le P M0 M1 f hf hfb n hn
    have hsub : {s : Fin n → X | Real.sqrt (variance f P) + τ
          < Real.sqrt (sampleVar (fun i => f (s i)))}
        ⊆ (fun (s : Fin n → X) (i : Fin n) => f (s i)) ⁻¹'
          {Z | Real.sqrt (∫ W, sampleVar W ∂(Measure.pi (fun _ : Fin n => P.map f))) + τ
            ≤ Real.sqrt (sampleVar Z)} := by
      intro s hs
      simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hs ⊢
      have := Real.sqrt_le_sqrt key
      linarith
    have hexp : (n : ℝ) * τ ^ 2 / (2 * (M1 - M0) ^ 2) = t := by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hM' : (M1 - M0) ≠ 0 := by linarith
      rw [hτ, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := Measure.le_map_apply hφ.aemeasurable _
      _ = _ := by rw [hpi]
      _ ≤ _ := sample_std_upper_tail (P.map f) M0 M1 hlt hP n hn τ hτ0
      _ = _ := by rw [hexp]
  · have hc : ∀ x, f x = M0 := fun x => le_antisymm (heq ▸ (hfb x).2) (hfb x).1
    have : {s : Fin n → X | Real.sqrt (variance f P) + (M1 - M0) * Real.sqrt (2 * t / n)
          < Real.sqrt (sampleVar (fun i => f (s i)))} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have : (fun i => f (s i)) = fun _ => M0 := funext fun i => hc _
      rw [this, sampleVar_const hn, Real.sqrt_zero, ← heq, sub_self, zero_mul, add_zero]
      exact Real.sqrt_nonneg _
    rw [this, measure_empty]
    exact bot_le


lemma det_chain (Eg yg Rg Rf yf Ef I δ u r v a b M t ρ ε n D : ℝ) (hn : 0 < n) (hM0 : 0 ≤ M)
    (hρt : 9 * t ≤ ρ) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (ha0 : 0 ≤ a) (hr0 : 0 ≤ r)
    (hru : 3 * u ≤ r) (hr2 : r ^ 2 = 2 * ρ / n)
    (h1 : Eg ≤ yg + 3 * (u * a) + 15 * M * t / n + D)
    (h4 : r * a - 2 * M * ρ / n ≤ Rg - yg) (hRgf : Rg ≤ Rf) (h5 : Rf - yf ≤ r * b)
    (h3 : b ≤ v + M * u) (h2 : yf ≤ Ef + u * v + 2 * M * t / (3 * n))
    (hfk : Ef + 2 * (r * v) < I + δ) :
    Eg ≤ I + δ + 19 * M * ρ / (3 * n) + D := by
  have hk : 0 ≤ M / n := div_nonneg hM0 hn.le
  have hρ0 : 0 ≤ ρ := by
    have : 0 ≤ r ^ 2 := sq_nonneg r
    rw [hr2] at this
    exact (div_nonneg_iff.mp this).elim (fun h => by linarith [h.1]) (fun h => by linarith [h.2])
  have hp0 : 0 ≤ M / n * ρ := mul_nonneg hk hρ0
  have hq : M / n * t ≤ M / n * ρ / 9 := by
    have := mul_le_mul_of_nonneg_left (show t ≤ ρ / 9 by linarith) hk
    linarith
  have hua : 3 * (u * a) ≤ r * a := by nlinarith
  have hrb : r * b ≤ r * v + r * (M * u) := by nlinarith
  have huv : u * v ≤ r * v := mul_le_mul_of_nonneg_right (by linarith) hv0
  have hrv : 0 ≤ r * v := mul_nonneg hr0 hv0
  have hru2 : r * u ≤ r * r / 3 := by nlinarith
  have hrr : r * r = 2 * (ρ / n) := by rw [← sq, hr2]; ring
  have hrum : r * (M * u) ≤ 2 / 3 * (M / n * ρ) := by
    have : M * (r * u) ≤ M * (r * r / 3) := mul_le_mul_of_nonneg_left hru2 hM0
    have e : M * (r * r / 3) = 2 / 3 * (M / n * ρ) := by rw [hrr]; ring
    nlinarith
  have e1 : 15 * M * t / n = 15 * (M / n * t) := by ring
  have e2 : 2 * M * t / (3 * n) = 2 / 3 * (M / n * t) := by field_simp
  have e3 : 2 * M * ρ / n = 2 * (M / n * ρ) := by ring
  have e4 : 19 * M * ρ / (3 * n) = 19 / 3 * (M / n * ρ) := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h4
  rw [e4]
  linarith

lemma bk_subset {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (M0 M1 : ℝ) (hM : M0 ≤ M1)
    (hF : ∀ f ∈ F, Measurable f ∧ ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t ρ ε : ℝ)
    (ht0 : 0 < t) (hρ : 9 * t ≤ ρ) (I δ : ℝ) (f : X → ℝ) (hfF : f ∈ F)
    (hfk : ∫ x, f x ∂P + 2 * Real.sqrt (2 * ρ / n * variance f P) < I + δ) :
    {s : Fin n → X | ∃ g ∈ F, (∀ f ∈ F, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
      I + δ + 19 * (M1 - M0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
        < ∫ x, g x ∂P}
    ⊆ {s : Fin n → X | ∃ f ∈ F, empMean f s + 3 * Real.sqrt (2 * empVar f s * t / n)
          + 15 * (M1 - M0) * t / n + 2 * (1 + 2 * Real.sqrt (2 * t / n)) * ε < ∫ x, f x ∂P}
      ∪ {s : Fin n → X | ∫ x, f x ∂P + Real.sqrt (2 * variance f P * t / n)
          + 2 * (M1 - M0) * t / (3 * n) < empMean f s}
      ∪ {s : Fin n → X | Real.sqrt (variance f P) + (M1 - M0) * Real.sqrt (2 * t / n)
          < Real.sqrt (sampleVar (fun i => f (s i)))} := by
  intro s hs
  obtain ⟨g, hgF, hmin, hlt⟩ := hs
  by_contra hcon
  simp only [Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  have h1g := h1 g hgF
  obtain ⟨hfm, hfb⟩ := hF f hfF
  obtain ⟨hgm, hgb⟩ := hF g hgF
  have hρ0 : 0 ≤ ρ := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC4g := two_sided_variance_bound n hn ρ hρ0 M0 M1 hM (fun i => g (s i))
    (fun i => hgb (s i))
  have hC4f := two_sided_variance_bound n hn ρ hρ0 M0 M1 hM (fun i => f (s i))
    (fun i => hfb (s i))
  have hRgf : robustRisk ρ g s ≤ robustRisk ρ f s := hmin f hfF
  unfold robustRisk at hRgf
  unfold empMean empVar at h1g
  unfold empMean at h2
  have hVar0 : 0 ≤ variance f P := variance_nonneg _ _
  have e1 : Real.sqrt (2 * sampleVar (fun i => g (s i)) * t / n)
      = Real.sqrt (2 * t / n) * Real.sqrt (sampleVar (fun i => g (s i))) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have e2 : Real.sqrt (2 * ρ / n * sampleVar (fun i => g (s i)))
      = Real.sqrt (2 * ρ / n) * Real.sqrt (sampleVar (fun i => g (s i))) :=
    Real.sqrt_mul (by positivity) _
  have e3 : Real.sqrt (2 * ρ / n * sampleVar (fun i => f (s i)))
      = Real.sqrt (2 * ρ / n) * Real.sqrt (sampleVar (fun i => f (s i))) :=
    Real.sqrt_mul (by positivity) _
  have e4 : Real.sqrt (2 * variance f P * t / n)
      = Real.sqrt (2 * t / n) * Real.sqrt (variance f P) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have e5 : Real.sqrt (2 * ρ / n * variance f P)
      = Real.sqrt (2 * ρ / n) * Real.sqrt (variance f P) :=
    Real.sqrt_mul (by positivity) _
  have hru : 3 * Real.sqrt (2 * t / n) ≤ Real.sqrt (2 * ρ / n) := by
    have h9 : (3 : ℝ) = Real.sqrt 9 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h9, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [show (9 : ℝ) * (2 * t / n) = (18 * t) / n by ring, div_le_div_iff_of_pos_right hnR]
    linarith
  have hr2 : Real.sqrt (2 * ρ / n) ^ 2 = 2 * ρ / n := Real.sq_sqrt (by positivity)
  rw [e1, show 2 * (1 + 2 * Real.sqrt (2 * t / n)) * ε = (2 + 4 * Real.sqrt (2 * t / n)) * ε
    by ring] at h1g
  rw [e4] at h2
  rw [e5] at hfk
  rw [e2] at hC4g
  rw [e3] at hC4f
  have h4 := le_trans (le_max_left _ _) hC4g.1
  have := det_chain _ _ _ _ _ _ I δ _ _ _ _ _ (M1 - M0) t ρ ε n _ hnR (by linarith) hρ
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hru hr2
    h1g h4 hRgf hC4f.2 h3 h2 hfk
  linarith

end RMOI

end VarianceRegularization.Covering

open VarianceRegularization.Covering VarianceRegularization.Covering.RMOI in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (F : Set (X → ℝ)) (hFne : F.Nonempty) (M0 M1 : ℝ) (hM : M0 ≤ M1)
    (hF : ∀ f ∈ F, Measurable f ∧ ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t ρ ε : ℝ)
    (hnt : 8 * (M1 - M0) ^ 2 / t ≤ n) (ht : Real.log 12 ≤ t) (hε : 0 < ε) (hρ : 9 * t ≤ ρ) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∃ g ∈ F, (∀ f ∈ F, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
          (⨅ f : F, (∫ x, (f : X → ℝ) x ∂P
              + 2 * Real.sqrt (2 * ρ / n * variance (f : X → ℝ) P)))
            + 19 * (M1 - M0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
            < ∫ x, g x ∂P}
      ≤ 2 * (3 * (empCoveringNumber F ε (2 * n) : ENNReal) + 1)
          * ENNReal.ofReal (Real.exp (-t)) := by
  haveI : Nonempty F := hFne.to_subtype
  have ht0 : 0 < t := lt_of_lt_of_le (Real.log_pos (by norm_num)) ht
  have hρ0 : 0 < ρ := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set I := ⨅ f : F, (∫ x, (f : X → ℝ) x ∂P + 2 * Real.sqrt (2 * ρ / n * variance (f : X → ℝ) P))
    with hI
  set e := ENNReal.ofReal (Real.exp (-t))
  set Bk : ℕ → Set (Fin n → X) := fun k => {s | ∃ g ∈ F,
      (∀ f ∈ F, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
      I + 1 / ((k : ℝ) + 1) + 19 * (M1 - M0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
        < ∫ x, g x ∂P} with hBk
  have hmono : Monotone Bk := by
    intro j k hjk s hs
    obtain ⟨g, hg, hmin, hlt⟩ := hs
    refine ⟨g, hg, hmin, lt_of_le_of_lt ?_ hlt⟩
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
    linarith
  have hcover : {s : Fin n → X | ∃ g ∈ F, (∀ f ∈ F, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
          I + 19 * (M1 - M0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
            < ∫ x, g x ∂P} ⊆ ⋃ k, Bk k := by
    intro s hs
    obtain ⟨g, hg, hmin, hlt⟩ := hs
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    refine Set.mem_iUnion.mpr ⟨k, g, hg, hmin, ?_⟩
    linarith
  -- uniform bounds on each `Bk k`
  have hC1 := uniform_empirical_bernstein P F M0 M1 hM hF n hn t ε hnt ht hε
  have hbound : ∀ k, Measure.pi (fun _ : Fin n => P) (Bk k)
      ≤ 2 * (3 * (empCoveringNumber F ε (2 * n) : ENNReal) + 1) * e := by
    intro k
    have hlt : I < I + 1 / ((k : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨⟨f, hfF⟩, hfk⟩ := exists_lt_of_ciInf_lt hlt
    simp only at hfk
    obtain ⟨hfm, hfb⟩ := hF f hfF
    have hC2 := fixed_function_bernstein P M0 M1 hM f hfm hfb n hn t ht0
    have hC3 := sample_std_tail_fn P M0 M1 hM f hfm hfb n hn t ht0
    set E1 := {s : Fin n → X | ∃ f ∈ F, empMean f s + 3 * Real.sqrt (2 * empVar f s * t / n)
          + 15 * (M1 - M0) * t / n + 2 * (1 + 2 * Real.sqrt (2 * t / n)) * ε < ∫ x, f x ∂P}
    set E2 := {s : Fin n → X | ∫ x, f x ∂P + Real.sqrt (2 * variance f P * t / n)
          + 2 * (M1 - M0) * t / (3 * n) < empMean f s}
    set E3 := {s : Fin n → X | Real.sqrt (variance f P) + (M1 - M0) * Real.sqrt (2 * t / n)
          < Real.sqrt (sampleVar (fun i => f (s i)))}
    have hsub : Bk k ⊆ E1 ∪ E2 ∪ E3 :=
      bk_subset P F M0 M1 hM hF n hn t ρ ε ht0 hρ I (1 / ((k : ℝ) + 1)) f hfF hfk
    calc Measure.pi (fun _ : Fin n => P) (Bk k)
        ≤ Measure.pi (fun _ : Fin n => P) (E1 ∪ E2 ∪ E3) := measure_mono hsub
      _ ≤ Measure.pi (fun _ : Fin n => P) E1 + Measure.pi (fun _ : Fin n => P) E2
          + Measure.pi (fun _ : Fin n => P) E3 := by
        refine le_trans (measure_union_le _ _) ?_
        gcongr
        exact measure_union_le _ _
      _ ≤ 6 * (empCoveringNumber F ε (2 * n) : ENNReal) * e + e + e := by
        gcongr
      _ = 2 * (3 * (empCoveringNumber F ε (2 * n) : ENNReal) + 1) * e := by ring
  calc _ ≤ Measure.pi (fun _ : Fin n => P) (⋃ k, Bk k) := measure_mono hcover
    _ = ⨆ k, Measure.pi (fun _ : Fin n => P) (Bk k) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hbound
