-- Prove2me | solution 1 for OWMR.arb_mean_demand
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:26.196207+00:00
-- url     : https://prove2.me/submissions/41c0d2fd-c58b-4c4c-838c-6b7fc06ed2ab

import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_F_properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Lemma C.1 (setup cost and mean demand), renewal form: for an `(s,S)` policy of positive width
`w = S - s`, `min(H,p) μ (M(w) - 1) ≤ ∫_{[0,w)} F(S - x) U(dx)`. Keeping one fresh demand inside
`F` and averaging the other `L` lead-time demands (Jensen), the cycle cost dominates the first and
last terms of the stopped walk, whose difference has mean `μ (M(w) - 1)` (Wald, via the product
structure of the first `N + 1` demands).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace OWMR.L1aux

variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ρ] in
lemma padHist_succ_zero {T : ℕ} (z : Fin (T + 1) → ℝ≥0) : padHist (T + 1) z 0 = z 0 := by
  simp only [padHist, dif_pos (Nat.succ_pos T)]
  rfl

omit [IsProbabilityMeasure ρ] in
lemma padHist_succ_shift {T : ℕ} (z : Fin (T + 1) → ℝ≥0) (i : ℕ) :
    padHist (T + 1) z (i + 1) = padHist T (Fin.tail z) i := by
  by_cases h : i < T
  · simp only [padHist, dif_pos (Nat.succ_lt_succ h), dif_pos h]
    rfl
  · simp only [padHist, dif_neg (fun h' => h (Nat.lt_of_succ_lt_succ h')), dif_neg h]

omit [IsProbabilityMeasure ρ] in
lemma measurable_padHistNN (T t : ℕ) : Measurable fun z : Fin T → ℝ≥0 => padHist T z t := by
  by_cases h : t < T
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply (⟨t, h⟩ : Fin T)
  · simp only [padHist, dif_neg h]
    exact measurable_const

omit [IsProbabilityMeasure ρ] in
lemma measurable_padHist (T t : ℕ) :
    Measurable fun z : Fin T → ℝ≥0 => ((padHist T z t : ℝ≥0) : ℝ) :=
  (measurable_padHistNN T t).coe_nnreal_real

omit [IsProbabilityMeasure ρ] in
lemma meas_psumH (T n : ℕ) :
    Measurable fun z : Fin T → ℝ≥0 => ∑ j ∈ Finset.range n, ((padHist T z j : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun j _ => measurable_padHist T j

lemma lintegral_pi_succ (T : ℕ) {F : ℝ≥0 × (Fin T → ℝ≥0) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ y, ∫⁻ z', F (y, z') ∂(Measure.pi fun _ : Fin T => ρ) ∂ρ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => ρ) 0
  have key : ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ z, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => ℝ≥0) 0 z)
          ∂(Measure.pi fun _ : Fin (T + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]

omit [IsProbabilityMeasure ρ] in
lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

lemma lintegral_law_zero {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) = F 0 := by
  rw [lintegral_map hF (measurable_psum 0)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, lintegral_const, measure_univ, mul_one]

lemma lintegral_law_succ (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin (n + 1) => ρ).map fun z => ∑ j, (z j : ℝ))
      = ∫⁻ y, ∫⁻ x, F ((y : ℝ) + x)
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ := by
  rw [lintegral_map hF (measurable_psum _)]
  have hG : Measurable fun q : ℝ≥0 × (Fin n → ℝ≥0) => F ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)) :=
    hF.comp (measurable_fst.coe_nnreal_real.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_snd).coe_nnreal_real))
  have key : ∫⁻ z, F (∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (n + 1) => ρ)
      = ∫⁻ z, F (((z 0 : ℝ≥0) : ℝ) + ∑ j, ((Fin.tail z j : ℝ≥0) : ℝ))
          ∂(Measure.pi fun _ : Fin (n + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [Fin.sum_univ_succ, Fin.tail]
  rw [key, lintegral_pi_succ ρ n hG]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map (f := fun x => F ((y : ℝ) + x)) (hF.comp (measurable_const_add _))
    (measurable_psum n)]

omit [IsProbabilityMeasure ρ] in
lemma psum_succ_shift {T : ℕ} (z : Fin (T + 1) → ℝ≥0) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ((padHist (T + 1) z j : ℝ≥0) : ℝ)
      = (z 0 : ℝ) + ∑ j ∈ Finset.range n, ((padHist T (Fin.tail z) j : ℝ≥0) : ℝ) := by
  rw [Finset.sum_range_succ', padHist_succ_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [padHist_succ_shift]

/-- The joint law of a partial sum and the next demand. -/
lemma law_pair : ∀ (n K : ℕ), n < K → ∀ (h : ℝ × ℝ≥0 → ℝ≥0∞), Measurable h →
    ∫⁻ z, h (∑ j ∈ Finset.range n, ((padHist K z j : ℝ≥0) : ℝ), padHist K z n)
        ∂(Measure.pi fun _ : Fin K => ρ)
      = ∫⁻ u, ∫⁻ x, h (u, x) ∂ρ ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ))
  | 0, K, hK, h, hh => by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have e : ∀ z : Fin (K' + 1) → ℝ≥0,
        h (∑ j ∈ Finset.range 0, ((padHist (K' + 1) z j : ℝ≥0) : ℝ), padHist (K' + 1) z 0)
        = (fun q : ℝ≥0 × (Fin K' → ℝ≥0) => h (0, q.1)) (z 0, Fin.tail z) := by
      intro z; simp [padHist_succ_zero]
    simp only [e]
    have hsplit := lintegral_pi_succ ρ K' (F := fun q : ℝ≥0 × (Fin K' → ℝ≥0) => h (0, q.1))
      (hh.comp (measurable_const.prodMk measurable_fst))
    simp only at hsplit
    rw [hsplit]
    have hFm : Measurable fun u : ℝ => ∫⁻ x, h (u, x) ∂ρ :=
      Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ≥0 => h q) hh
    rw [lintegral_law_zero ρ hFm]
    simp [lintegral_const, measure_univ]
  | n + 1, K, hK, h, hh => by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have e : ∀ z : Fin (K' + 1) → ℝ≥0,
        h (∑ j ∈ Finset.range (n + 1), ((padHist (K' + 1) z j : ℝ≥0) : ℝ),
          padHist (K' + 1) z (n + 1))
        = (fun q : ℝ≥0 × (Fin K' → ℝ≥0) => h ((q.1 : ℝ)
            + ∑ j ∈ Finset.range n, ((padHist K' q.2 j : ℝ≥0) : ℝ), padHist K' q.2 n))
          (z 0, Fin.tail z) := by
      intro z
      simp only
      rw [psum_succ_shift, padHist_succ_shift]
    simp only [e]
    have hF : Measurable fun q : ℝ≥0 × (Fin K' → ℝ≥0) => h ((q.1 : ℝ)
        + ∑ j ∈ Finset.range n, ((padHist K' q.2 j : ℝ≥0) : ℝ), padHist K' q.2 n) :=
      hh.comp ((measurable_fst.coe_nnreal_real.add ((meas_psumH K' n).comp measurable_snd)).prodMk
        ((measurable_padHistNN K' n).comp measurable_snd))
    have hsplit := lintegral_pi_succ ρ K' hF
    simp only at hsplit
    rw [hsplit]
    have ih : ∀ y : ℝ≥0, ∫⁻ z', h ((y : ℝ)
        + ∑ j ∈ Finset.range n, ((padHist K' z' j : ℝ≥0) : ℝ), padHist K' z' n)
          ∂(Measure.pi fun _ : Fin K' => ρ)
        = ∫⁻ u, ∫⁻ x, h ((y : ℝ) + u, x) ∂ρ
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) := fun y =>
      law_pair n K' (by omega) (fun q => h ((y : ℝ) + q.1, q.2))
        (hh.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
    simp only [ih]
    have hFm : Measurable fun u : ℝ => ∫⁻ x, h (u, x) ∂ρ :=
      Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ≥0 => h q) hh
    rw [lintegral_law_succ ρ n hFm]

omit [IsProbabilityMeasure ρ] in
/-- Pathwise: the first and last terms of the stopped walk dominate its demand span. -/
lemma pathwise (d : ℕ → ℝ≥0) (a w : ℝ) : ∀ N : ℕ,
    ∑ n ∈ Finset.range N,
        (if ∑ j ∈ Finset.range (n + 1), (d j : ℝ) < w then (d (n + 1) : ℝ) else 0)
      ≤ ∑ n ∈ Finset.range (N + 1), (if ∑ j ∈ Finset.range n, (d j : ℝ) < w
          then |a - ∑ j ∈ Finset.range (n + 1), (d j : ℝ)| else 0) := by
  have hmono : ∀ n m, n ≤ m → ∑ j ∈ Finset.range n, (d j : ℝ) ≤ ∑ j ∈ Finset.range m, (d j : ℝ) :=
    fun n m hnm => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      fun j _ _ => NNReal.coe_nonneg _
  intro N
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact Finset.sum_nonneg fun n _ => by split_ifs <;> simp [abs_nonneg]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ _ (N + 1)]
    by_cases hN : ∑ j ∈ Finset.range (N + 1), (d j : ℝ) < w
    · -- every earlier partial sum is below `w`
      have hall : ∀ n ≤ N + 1, ∑ j ∈ Finset.range n, (d j : ℝ) < w := fun n hn =>
        lt_of_le_of_lt (hmono n (N + 1) hn) hN
      have hL : ∑ n ∈ Finset.range N,
          (if ∑ j ∈ Finset.range (n + 1), (d j : ℝ) < w then (d (n + 1) : ℝ) else 0)
          = ∑ n ∈ Finset.range N, (d (n + 1) : ℝ) :=
        Finset.sum_congr rfl fun n hn => by
          rw [if_pos (hall (n + 1) (by simp at hn; omega))]
      have hR : ∑ n ∈ Finset.range (N + 1), (if ∑ j ∈ Finset.range n, (d j : ℝ) < w
          then |a - ∑ j ∈ Finset.range (n + 1), (d j : ℝ)| else 0)
          = ∑ n ∈ Finset.range (N + 1), |a - ∑ j ∈ Finset.range (n + 1), (d j : ℝ)| :=
        Finset.sum_congr rfl fun n hn => by
          rw [if_pos (hall n (by simp at hn; omega))]
      rw [hL, hR, if_pos hN, if_pos hN]
      -- span = S(N+2) - S(1)
      have hspan : ∑ n ∈ Finset.range N, (d (n + 1) : ℝ) + (d (N + 1) : ℝ)
          = ∑ j ∈ Finset.range (N + 2), (d j : ℝ) - ∑ j ∈ Finset.range 1, (d j : ℝ) := by
        rw [← Finset.sum_range_succ (fun n => (d (n + 1) : ℝ)) N]
        rw [Finset.sum_range_succ' (fun j => (d j : ℝ)) (N + 1)]
        simp
      rw [hspan]
      have h0 : |a - ∑ j ∈ Finset.range 1, (d j : ℝ)|
          ≤ ∑ n ∈ Finset.range (N + 1), |a - ∑ j ∈ Finset.range (n + 1), (d j : ℝ)| :=
        Finset.single_le_sum (f := fun n => |a - ∑ j ∈ Finset.range (n + 1), (d j : ℝ)|)
          (fun n _ => abs_nonneg _) (Finset.mem_range.2 (Nat.succ_pos N))
      have htri : ∑ j ∈ Finset.range (N + 2), (d j : ℝ) - ∑ j ∈ Finset.range 1, (d j : ℝ)
          ≤ |a - ∑ j ∈ Finset.range 1, (d j : ℝ)| + |a - ∑ j ∈ Finset.range (N + 1 + 1), (d j : ℝ)| := by
        have := abs_sub_le (∑ j ∈ Finset.range (N + 2), (d j : ℝ)) a (∑ j ∈ Finset.range 1, (d j : ℝ))
        rw [abs_sub_comm (∑ j ∈ Finset.range (N + 2), (d j : ℝ)) a] at this
        have h2 := le_abs_self (∑ j ∈ Finset.range (N + 2), (d j : ℝ) - ∑ j ∈ Finset.range 1, (d j : ℝ))
        linarith
      linarith
    · rw [if_neg hN, if_neg hN]
      linarith

end OWMR.L1aux

namespace OWMR.L1aux

lemma int_marg {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

lemma int_sumL {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ)) (Measure.pi fun _ : Fin L => N.marginal i) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.marginal i) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 (int_marg N hN i)

lemma mean_sumL {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (L : ℕ) :
    ∫ z, ∑ j, (z j : ℝ) ∂(Measure.pi fun _ : Fin L => N.marginal i)
      = L * ∫ x, (x : ℝ) ∂(N.marginal i) := by
  rw [integral_finsetSum _ fun j _ => ?_]
  · have hj : ∀ j : Fin L, ∫ z : Fin L → ℝ≥0, (z j : ℝ) ∂(Measure.pi fun _ : Fin L => N.marginal i)
        = ∫ x, (x : ℝ) ∂(N.marginal i) := by
      intro j
      have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.marginal i) j
      have h1 := integral_map (μ := Measure.pi fun _ : Fin L => N.marginal i)
        (φ := Function.eval j) (f := fun x : ℝ≥0 => (x : ℝ)) (measurable_pi_apply j).aemeasurable
        measurable_coe_nnreal_real.aestronglyMeasurable
      rw [hmp.map_eq] at h1
      exact h1.symm
    simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.marginal i) j
    exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 (int_marg N hN i)

/-- Jensen over the last `L` lead-time demands, keeping the first one. -/
lemma jensen_step {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (b : ℝ) :
    ∫⁻ x, ENNReal.ofReal (min (N.H i) N.p
        * |b - N.L i * (∫ y, (y : ℝ) ∂(N.marginal i)) - x|) ∂(N.marginal i)
      ≤ ENNReal.ofReal (N.F i b) := by
  set ρ := N.marginal i with hρ
  set L := N.L i with hL
  set μ := ∫ y, (y : ℝ) ∂ρ with hμ
  set c := min (N.H i) N.p with hc
  have hH := (hN.H_pos i).le
  have hp := hN.p_pos.le
  have hc0 : 0 ≤ c := le_min hH hp
  set φ : ℝ → ℝ := fun t => N.H i * max t 0 + N.p * max (-t) 0 with hφdef
  have hφc : ∀ t, c * |t| ≤ φ t := by
    intro t
    have e : |t| = max t 0 + max (-t) 0 := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
    rw [e]
    have a1 : c * max t 0 ≤ N.H i * max t 0 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (le_max_right _ _)
    have a2 : c * max (-t) 0 ≤ N.p * max (-t) 0 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (le_max_right _ _)
    show c * (max t 0 + max (-t) 0) ≤ N.H i * max t 0 + N.p * max (-t) 0
    linarith
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => add_nonneg (mul_nonneg hH (le_max_right _ _))
    (mul_nonneg hp (le_max_right _ _))
  have hφcont : Continuous φ := by rw [hφdef]; fun_prop
  have huL1 := int_sumL N hN i (L + 1)
  have hint : Integrable (fun z : Fin (L + 1) → ℝ≥0 => φ (b - ∑ j, (z j : ℝ)))
      (Measure.pi fun _ : Fin (L + 1) => ρ) := by
    refine Integrable.mono' (((integrable_const b).sub huL1).norm.const_mul (N.H i + N.p))
      (hφcont.comp_aestronglyMeasurable ((integrable_const b).sub huL1).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _), Real.norm_eq_abs]
    show N.H i * max (b - ∑ j, (z j : ℝ)) 0 + N.p * max (-(b - ∑ j, (z j : ℝ))) 0
      ≤ (N.H i + N.p) * |b - ∑ j, (z j : ℝ)|
    have a1 : max (b - ∑ j, (z j : ℝ)) 0 ≤ |b - ∑ j, (z j : ℝ)| := max_le (le_abs_self _) (abs_nonneg _)
    have a2 : max (-(b - ∑ j, (z j : ℝ))) 0 ≤ |b - ∑ j, (z j : ℝ)| := max_le (neg_le_abs _) (abs_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left a1 hH, mul_le_mul_of_nonneg_left a2 hp]
  have hF : N.F i b = ∫ z, φ (b - ∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (L + 1) => ρ) := by
    rw [Network.F]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hφdef, neg_sub]
    rfl
  rw [hF, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => hφ0 _)]
  have hsplit : ∀ z : Fin (L + 1) → ℝ≥0, ENNReal.ofReal (φ (b - ∑ j, (z j : ℝ)))
      = (fun q : ℝ≥0 × (Fin L → ℝ≥0) => ENNReal.ofReal (φ (b - ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)))))
        (z 0, Fin.tail z) := by
    intro z
    simp [Fin.sum_univ_succ, Fin.tail]
  simp only [hsplit]
  have hmF : Measurable fun q : ℝ≥0 × (Fin L → ℝ≥0) =>
      ENNReal.ofReal (φ (b - ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)))) :=
    ENNReal.measurable_ofReal.comp (hφcont.measurable.comp (measurable_const.sub
      (measurable_fst.coe_nnreal_real.add ((measurable_psum L).comp measurable_snd))))
  have h2 := lintegral_pi_succ ρ L hmF
  simp only at h2
  rw [h2]
  refine lintegral_mono fun y => ?_
  -- inner Jensen
  have huL := int_sumL N hN i L
  have hyz : Integrable (fun z : Fin L → ℝ≥0 => (y : ℝ) + ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin L => ρ) := (integrable_const _).add huL
  have hg : Integrable (fun z : Fin L → ℝ≥0 => b - ((y : ℝ) + ∑ j, (z j : ℝ)))
      (Measure.pi fun _ : Fin L => ρ) := (integrable_const _).sub hyz
  calc ENNReal.ofReal (c * |b - L * μ - (y : ℝ)|)
      = ENNReal.ofReal (c * |∫ z, (b - ((y : ℝ) + ∑ j, (z j : ℝ))) ∂(Measure.pi fun _ : Fin L => ρ)|) := by
        rw [integral_sub (integrable_const b) hyz, integral_add (integrable_const _) huL,
          mean_sumL N hN i L]
        simp only [integral_const, probReal_univ, one_smul]
        rw [← hμ]
        congr 2; ring_nf
    _ ≤ ENNReal.ofReal (∫ z, c * |b - ((y : ℝ) + ∑ j, (z j : ℝ))| ∂(Measure.pi fun _ : Fin L => ρ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) hc0
    _ = ∫⁻ z, ENNReal.ofReal (c * |b - ((y : ℝ) + ∑ j, (z j : ℝ))|) ∂(Measure.pi fun _ : Fin L => ρ) :=
        ofReal_integral_eq_lintegral_ofReal (hg.abs.const_mul c)
          (Filter.Eventually.of_forall fun z => mul_nonneg hc0 (abs_nonneg _))
    _ ≤ ∫⁻ z, ENNReal.ofReal (φ (b - ((y : ℝ) + ∑ j, (z j : ℝ)))) ∂(Measure.pi fun _ : Fin L => ρ) :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hφc _)

end OWMR.L1aux

open OWMR.L1aux in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (s S : ℝ) (hsS : s < S) :
    min (N.H i) N.p * (∫ x, (x : ℝ) ∂(N.marginal i))
        * ((renewalMeasure (N.marginal i) (Set.Ico 0 (S - s))).toReal - 1)
      ≤ ∫ x in Set.Ico 0 (S - s), N.F i (S - x) ∂(renewalMeasure (N.marginal i)) := by
  set ρ := N.marginal i with hρ
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = S - s := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : 0 < w := by rw [hw]; linarith
  set μ := ∫ x, (x : ℝ) ∂ρ with hμ
  set c := min (N.H i) N.p with hc
  set a := S - N.L i * μ with ha
  set law : ℕ → Measure ℝ := fun k => (Measure.pi fun _ : Fin k => ρ).map fun z => ∑ j, (z j : ℝ)
    with hlaw
  have hH := (hN.H_pos i).le
  have hp := hN.p_pos.le
  have hc0 : 0 ≤ c := le_min hH hp
  have hμ0 : 0 ≤ μ := integral_nonneg fun x => NNReal.coe_nonneg x
  have hint := int_marg N hN i
  have hmean : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ := by
    rw [hρ]; unfold Network.marginal
    rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
    exact hN.mean_pos i
  have hUe_top : renewalMeasure ρ (Set.Ico 0 w) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hmean w).ne
  -- `G(u) ≤ F(S - u)`
  have hG : ∀ u : ℝ, ∫⁻ x, ENNReal.ofReal (c * |a - u - x|) ∂ρ
      ≤ ENNReal.ofReal (N.F i (S - u)) := by
    intro u
    have := jensen_step N hN i (S - u)
    rw [← hρ, ← hμ] at this
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) this
    rw [ha]; congr 2; ring_nf
  have hcx : ∫⁻ x, ENNReal.ofReal (c * (x : ℝ)) ∂ρ = ENNReal.ofReal (c * μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul c)
      (Filter.Eventually.of_forall fun x => mul_nonneg hc0 (NNReal.coe_nonneg x)),
      integral_const_mul]
  set I := ∫⁻ u in Set.Ico 0 w, ENNReal.ofReal (N.F i (S - u)) ∂(renewalMeasure ρ) with hI
  have hmeasG : Measurable fun u : ℝ => ∫⁻ x, ENNReal.ofReal (c * |a - u - x|) ∂ρ :=
    Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ≥0 => ENNReal.ofReal (c * |a - q.1 - q.2|))
      (by fun_prop)
  have htrunc : ∀ M : ℕ, ENNReal.ofReal (c * μ) * ∑ k ∈ Finset.range M, law (k + 1) (Set.Ico 0 w)
      ≤ I := by
    intro M
    set π := Measure.pi fun _ : Fin (M + 1) => ρ with hπ
    set Sk : (Fin (M + 1) → ℝ≥0) → ℕ → ℝ := fun z k =>
      ∑ j ∈ Finset.range k, ((padHist (M + 1) z j : ℝ≥0) : ℝ) with hSk
    have hSk0 : ∀ z k, 0 ≤ Sk z k := fun z k => Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _
    -- the expectation of each truncated term
    have hterm : ∀ k < M + 1,
        ∫⁻ u, (Set.Ico 0 w).indicator (fun u => ∫⁻ x, ENNReal.ofReal (c * |a - u - x|) ∂ρ) u
          ∂(law k)
        = ∫⁻ z, (if Sk z k < w then ENNReal.ofReal (c * |a - Sk z (k + 1)|) else 0) ∂π := by
      intro k hk
      have hh : Measurable fun q : ℝ × ℝ≥0 =>
          if q.1 ∈ Set.Ico (0 : ℝ) w then ENNReal.ofReal (c * |a - q.1 - q.2|) else 0 :=
        Measurable.ite (measurableSet_Ico.preimage measurable_fst) (by fun_prop) measurable_const
      have h1 := law_pair ρ k (M + 1) hk _ hh
      refine (Eq.trans ?_ h1.symm).trans ?_
      · refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ Set.Ico (0 : ℝ) w
        · simp only [Set.indicator_of_mem hu, if_pos hu]
        · simp only [Set.indicator_of_notMem hu, if_neg hu, lintegral_zero]
      · refine lintegral_congr fun z => ?_
        have hsplit : Sk z (k + 1) = Sk z k + ((padHist (M + 1) z k : ℝ≥0) : ℝ) := by
          simp only [hSk]; rw [Finset.sum_range_succ]
        by_cases hlt : Sk z k < w
        · have hmem : Sk z k ∈ Set.Ico (0 : ℝ) w := ⟨hSk0 z k, hlt⟩
          simp only [hSk] at hmem hlt
          rw [if_pos hmem, if_pos hlt, hsplit]
          simp only [hSk]
          congr 2; ring_nf
        · have hmem : Sk z k ∉ Set.Ico (0 : ℝ) w := fun h => hlt h.2
          simp only [hSk] at hmem hlt
          rw [if_neg hmem, if_neg hlt]
    have hdemand : ∀ k < M,
        ∫⁻ z, (if Sk z (k + 1) < w then ENNReal.ofReal (c * ((padHist (M + 1) z (k + 1) : ℝ≥0) : ℝ))
          else 0) ∂π = ENNReal.ofReal (c * μ) * law (k + 1) (Set.Ico 0 w) := by
      intro k hk
      have hh : Measurable fun q : ℝ × ℝ≥0 =>
          if q.1 ∈ Set.Ico (0 : ℝ) w then ENNReal.ofReal (c * (q.2 : ℝ)) else 0 :=
        Measurable.ite (measurableSet_Ico.preimage measurable_fst) (by fun_prop) measurable_const
      have h1 := law_pair ρ (k + 1) (M + 1) (by omega) _ hh
      refine (Eq.trans ?_ h1).trans ?_
      · refine lintegral_congr fun z => ?_
        by_cases hlt : Sk z (k + 1) < w
        · have hmem : Sk z (k + 1) ∈ Set.Ico (0 : ℝ) w := ⟨hSk0 z (k + 1), hlt⟩
          simp only [hSk] at hmem hlt
          rw [if_pos hlt, if_pos hmem]
        · have hmem : Sk z (k + 1) ∉ Set.Ico (0 : ℝ) w := fun h => hlt h.2
          simp only [hSk] at hmem hlt
          rw [if_neg hlt, if_neg hmem]
      · have e : ∀ u : ℝ, ∫⁻ x, (if u ∈ Set.Ico (0 : ℝ) w then ENNReal.ofReal (c * (x : ℝ)) else 0) ∂ρ
            = (Set.Ico 0 w).indicator (fun _ => ENNReal.ofReal (c * μ)) u := by
          intro u
          by_cases hu : u ∈ Set.Ico (0 : ℝ) w
          · simp only [if_pos hu, Set.indicator_of_mem hu, hcx]
          · simp only [if_neg hu, Set.indicator_of_notMem hu, lintegral_zero]
        simp only [e]
        rw [lintegral_indicator_const measurableSet_Ico]
    -- assemble
    have hmeasT : ∀ k, Measurable fun z : Fin (M + 1) → ℝ≥0 =>
        (if Sk z k < w then ENNReal.ofReal (c * |a - Sk z (k + 1)|) else 0) := fun k =>
      Measurable.ite (measurableSet_lt (meas_psumH (M + 1) k) measurable_const)
        (ENNReal.measurable_ofReal.comp (measurable_const.mul
          (continuous_abs.measurable.comp (measurable_const.sub (meas_psumH (M + 1) (k + 1))))))
        measurable_const
    have hmeasD : ∀ k, Measurable fun z : Fin (M + 1) → ℝ≥0 =>
        (if Sk z (k + 1) < w then ENNReal.ofReal (c * ((padHist (M + 1) z (k + 1) : ℝ≥0) : ℝ))
          else 0) := fun k =>
      Measurable.ite (measurableSet_lt (meas_psumH (M + 1) (k + 1)) measurable_const)
        (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_padHist (M + 1) (k + 1))))
        measurable_const
    calc ENNReal.ofReal (c * μ) * ∑ k ∈ Finset.range M, law (k + 1) (Set.Ico 0 w)
        = ∑ k ∈ Finset.range M, ∫⁻ z, (if Sk z (k + 1) < w
            then ENNReal.ofReal (c * ((padHist (M + 1) z (k + 1) : ℝ≥0) : ℝ)) else 0) ∂π := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k hk => (hdemand k (Finset.mem_range.1 hk)).symm
      _ = ∫⁻ z, ∑ k ∈ Finset.range M, (if Sk z (k + 1) < w
            then ENNReal.ofReal (c * ((padHist (M + 1) z (k + 1) : ℝ≥0) : ℝ)) else 0) ∂π :=
          (lintegral_finsetSum _ fun k _ => hmeasD k).symm
      _ ≤ ∫⁻ z, ∑ k ∈ Finset.range (M + 1),
            (if Sk z k < w then ENNReal.ofReal (c * |a - Sk z (k + 1)|) else 0) ∂π := by
          refine lintegral_mono fun z => ?_
          have hpw := pathwise (padHist (M + 1) z) a w M
          have hpw' := mul_le_mul_of_nonneg_left hpw hc0
          rw [Finset.mul_sum, Finset.mul_sum] at hpw'
          have e1 : ∀ k ∈ Finset.range M, (if Sk z (k + 1) < w
              then ENNReal.ofReal (c * ((padHist (M + 1) z (k + 1) : ℝ≥0) : ℝ)) else 0)
              = ENNReal.ofReal (c * (if Sk z (k + 1) < w
                  then ((padHist (M + 1) z (k + 1) : ℝ≥0) : ℝ) else 0)) := fun k _ => by
            split_ifs <;> simp
          have e2 : ∀ k ∈ Finset.range (M + 1), (if Sk z k < w
              then ENNReal.ofReal (c * |a - Sk z (k + 1)|) else 0)
              = ENNReal.ofReal (c * (if Sk z k < w then |a - Sk z (k + 1)| else 0)) := fun k _ => by
            split_ifs <;> simp
          rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
            ← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hc0 (by split_ifs <;> simp)),
            ← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hc0 (by split_ifs <;> simp [abs_nonneg]))]
          exact ENNReal.ofReal_le_ofReal hpw'
      _ = ∑ k ∈ Finset.range (M + 1), ∫⁻ z,
            (if Sk z k < w then ENNReal.ofReal (c * |a - Sk z (k + 1)|) else 0) ∂π :=
          lintegral_finsetSum _ fun k _ => hmeasT k
      _ = ∑ k ∈ Finset.range (M + 1), ∫⁻ u, (Set.Ico 0 w).indicator
            (fun u => ∫⁻ x, ENNReal.ofReal (c * |a - u - x|) ∂ρ) u ∂(law k) :=
          Finset.sum_congr rfl fun k hk => (hterm k (Finset.mem_range.1 hk)).symm
      _ ≤ ∑' k, ∫⁻ u, (Set.Ico 0 w).indicator
            (fun u => ∫⁻ x, ENNReal.ofReal (c * |a - u - x|) ∂ρ) u ∂(law k) :=
          ENNReal.sum_le_tsum _
      _ = ∫⁻ u in Set.Ico 0 w, ∫⁻ x, ENNReal.ofReal (c * |a - u - x|) ∂ρ ∂(renewalMeasure ρ) := by
          rw [← lintegral_indicator measurableSet_Ico]
          exact (lintegral_sum_measure _ _).symm
      _ ≤ I := setLIntegral_mono' measurableSet_Ico fun u _ => hG u
  -- `U[0,w) = 1 + ∑_{k ≥ 0} law (k+1) [0,w)`
  have hUsplit : renewalMeasure ρ (Set.Ico 0 w)
      = 1 + ∑' k, law (k + 1) (Set.Ico 0 w) := by
    have h1 : renewalMeasure ρ (Set.Ico 0 w) = ∑' k, law k (Set.Ico 0 w) :=
      Measure.sum_apply _ measurableSet_Ico
    rw [h1, tsum_eq_zero_add' ENNReal.summable]
    congr 1
    show ((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) (Set.Ico 0 w) = 1
    rw [Measure.map_apply (measurable_psum 0) measurableSet_Ico]
    have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
      ext z; simp [hw0]
    rw [this, measure_univ]
  have htail : ENNReal.ofReal (c * μ) * ∑' k, law (k + 1) (Set.Ico 0 w) ≤ I := by
    rw [ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
    exact iSup_le htrunc
  -- back to real numbers
  have hFc : Continuous (N.F i) := by
    obtain ⟨-, -, hFlip, -⟩ := F_properties N hN i
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine Metric.continuousAt_iff.2 fun ε hε =>
      ⟨ε / (N.H i + N.p + 1), by positivity, fun y' hy' => ?_⟩
    rw [Real.dist_eq] at hy' ⊢
    calc |N.F i y' - N.F i y| ≤ (N.H i + N.p) * |y' - y| := hFlip y' y
      _ ≤ (N.H i + N.p) * (ε / (N.H i + N.p + 1)) := by gcongr
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨hF0, -, hFlip, -⟩ := F_properties N hN i
  have hIF : IntegrableOn (fun x => N.F i (S - x)) (Set.Ico 0 w) (renewalMeasure ρ) := by
    refine Measure.integrableOn_of_bounded hUe_top
      (hFc.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (M := N.F i S + (N.H i + N.p) * w)
      ((ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    have := hFlip (S - x) S
    rw [abs_le] at this
    have hx' : |S - x - S| ≤ w := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    nlinarith [mul_le_mul_of_nonneg_left hx' (by linarith : (0 : ℝ) ≤ N.H i + N.p)]
  have hBoch : ∫ x in Set.Ico 0 w, N.F i (S - x) ∂(renewalMeasure ρ) = I.toReal := by
    rw [hI, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => hF0 _)
      hIF.aestronglyMeasurable]
  have hItop : I ≠ ∞ := by
    rw [hI, ← ofReal_integral_eq_lintegral_ofReal hIF
      (Filter.Eventually.of_forall fun x => hF0 _)]
    exact ENNReal.ofReal_ne_top
  rw [hBoch]
  have htsum_top : ∑' k, law (k + 1) (Set.Ico 0 w) ≠ ∞ := by
    intro h
    rw [h, add_top] at hUsplit
    exact hUe_top hUsplit
  have hUreal : (renewalMeasure ρ (Set.Ico 0 w)).toReal - 1 = (∑' k, law (k + 1) (Set.Ico 0 w)).toReal := by
    rw [hUsplit, ENNReal.toReal_add ENNReal.one_ne_top htsum_top]; simp
  rw [hUreal]
  have := ENNReal.toReal_mono hItop htail
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hc0 hμ0)] at this
  linarith
