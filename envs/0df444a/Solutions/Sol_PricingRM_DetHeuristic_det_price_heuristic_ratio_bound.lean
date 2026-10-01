-- Prove2me | solution 1 for PricingRM.DetHeuristic.det_price_heuristic_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:20:15.540915+00:00
-- url     : https://prove2.me/submissions/b89358d4-37e9-445d-bd39-3f132ebdc2c5

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

set_option autoImplicit false

namespace PricingRM.DetHeuristic.P21cc

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic
open scoped ENNReal

lemma meanDemand_nonneg {N : ℕ} (M : PricingModel N) (n : Fin N) (p : ℝ) :
    0 ≤ meanDemand M n p :=
  integral_nonneg_of_ae (M.nonneg n p)

/-- A concave function that is nonnegative on `[0, ∞)` is monotone there. -/
lemma conc_mono {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : f a ≤ f b := by
  by_contra hlt
  rw [not_le] at hlt
  have hab' : a < b := lt_of_le_of_ne hab (by rintro rfl; exact lt_irrefl _ hlt)
  have hdpos : 0 < f a - f b := by linarith
  have hfb : 0 ≤ f b := h0 b (by linarith)
  have hfa : 0 ≤ f a := h0 a ha
  have hX : 0 ≤ b * f a / (f a - f b) := div_nonneg (mul_nonneg (by linarith) hfa) hdpos.le
  set q := b + 1 + b * f a / (f a - f b) with hq
  have hbq : b < q := by linarith
  have hqa : 0 < q - a := by linarith
  have hfq : 0 ≤ f q := h0 q (by linarith)
  have key := hf.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ q))
    (div_nonneg (by linarith : (0:ℝ) ≤ q - b) hqa.le)
    (div_nonneg (by linarith : (0:ℝ) ≤ b - a) hqa.le)
    (by rw [← add_div, show q - b + (b - a) = q - a by ring, div_self hqa.ne'])
  have hpt : ((q - b) / (q - a)) • a + ((b - a) / (q - a)) • q = b := by
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hqa.ne']; ring
  rw [hpt] at key
  simp only [smul_eq_mul] at key
  have key2 : (q - b) * f a + (b - a) * f q ≤ (q - a) * f b := by
    have h := mul_le_mul_of_nonneg_left key hqa.le
    have e1 : (q - a) * ((q - b) / (q - a) * f a + (b - a) / (q - a) * f q)
        = (q - b) * f a + (b - a) * f q := by field_simp
    linarith
  have hqd : (q - b) * f a - (q - a) * f b = (b + 1) * (f a - f b) + a * f b := by
    have : b * f a / (f a - f b) * (f a - f b) = b * f a := div_mul_cancel₀ _ hdpos.ne'
    rw [hq]; nlinarith [this]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b - a) hfq, mul_nonneg ha hfb]

/-- Mean demand is antitone on `[0, ∞)` under the concavity/convexity hypotheses. -/
lemma md_anti {m : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Ici 0) m)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (fun p => p * m p))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : m b ≤ m a := by
  have pos : ∀ a b : ℝ, 0 < a → a ≤ b → m b ≤ m a := by
    intro a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have key := hconc.2 (Set.mem_Ici.mpr hb.le) (Set.mem_Ici.mpr le_rfl)
      (div_nonneg ha.le hb.le) (sub_nonneg.mpr ((div_le_one hb).mpr hab)) (by ring)
    have e : (a / b) • b + (1 - a / b) • (0:ℝ) = a := by
      simp only [smul_eq_mul, mul_zero, add_zero]; exact div_mul_cancel₀ a hb.ne'
    rw [e] at key
    simp only [smul_eq_mul, zero_mul, mul_zero, add_zero] at key
    have e2 : a / b * (b * m b) = a * m b := by field_simp
    rw [e2] at key
    exact le_of_mul_le_mul_left key ha
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    rcases eq_or_lt_of_le hab with h' | h'
    · rw [← h']
    · have h2 := pos b (2 * b) h' (by linarith)
      have key := hconv.2 (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ 2 * b)) (Set.mem_Ici.mpr le_rfl)
        (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
      have e : (1 / 2 : ℝ) • (2 * b) + (1 / 2 : ℝ) • (0:ℝ) = b := by
        simp only [smul_eq_mul]; ring
      rw [e] at key
      simp only [smul_eq_mul] at key
      linarith
  · exact pos a b h hab

lemma rev_le_opt {N : ℕ} (M : PricingModel N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    {C₀ : ℝ} {pdet : Fin N → ℝ} (hopt : IsDetOptimal M C₀ pdet) (n : Fin N) {p : ℝ}
    (hp : 0 ≤ p) :
    p * meanDemand M n p ≤ pdet n * meanDemand M n (pdet n) := by
  classical
  have hpd : 0 ≤ pdet n := hopt.1.1 n
  set q := max p (pdet n) with hqdef
  have hq : 0 ≤ q := le_max_of_le_left hp
  have h1 : p * meanDemand M n p ≤ q * meanDemand M n q :=
    conc_mono (hconc n) (fun x hx => mul_nonneg hx (meanDemand_nonneg M n x)) hp
      (le_max_left _ _)
  have hmq : meanDemand M n q ≤ meanDemand M n (pdet n) :=
    md_anti (hconv n) (hconc n) hpd (le_max_right _ _)
  set p' := Function.update pdet n q with hp'
  have hfeas : DetFeasible M C₀ p' := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = n
      · subst h; simp [p', hq]
      · simp [p', h, hopt.1.1 i]
    · refine le_trans (Finset.sum_le_sum fun i _ => ?_) hopt.1.2
      by_cases h : i = n
      · subst h; simp [p', hmq]
      · simp [p', h]
  have h2 := hopt.2 p' hfeas
  unfold detObjective at h2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ n)] at h2
  have hrest : ∑ x ∈ Finset.univ.erase n, p' x * meanDemand M x (p' x)
      = ∑ x ∈ Finset.univ.erase n, pdet x * meanDemand M x (pdet x) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ≠ n := Finset.ne_of_mem_erase hi
    simp [p', this]
  rw [hrest] at h2
  have hpn : p' n = q := by simp [p']
  rw [hpn] at h2
  linarith

/-- Upper bound on the Bellman value. -/
lemma value_le {N : ℕ} (M : PricingModel N) (R : Fin N → ℝ)
    (hR : ∀ n p, 0 ≤ p → p * meanDemand M n p ≤ R n) :
    ∀ (k : ℕ) (hk : k ≤ N) (C : ℝ), valueToGo M k hk C ≤
      ∑ n ∈ Finset.univ.filter (fun n : Fin N => N - k ≤ n.val), ENNReal.ofReal (R n) := by
  intro k
  induction k with
  | zero =>
    intro hk C
    simp [valueToGo]
  | succ k ih =>
    intro hk C
    rw [valueToGo]
    refine iSup₂_le fun p hp => ?_
    have hp' : 0 ≤ p := hp
    have hsplit : Finset.univ.filter (fun n : Fin N => N - (k + 1) ≤ n.val) =
        insert ⟨N - (k + 1), by omega⟩ (Finset.univ.filter (fun n : Fin N => N - k ≤ n.val)) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]; omega
    have hj : (⟨N - (k + 1), by omega⟩ : Fin N) ∉
        Finset.univ.filter (fun n : Fin N => N - k ≤ n.val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [hsplit, Finset.sum_insert hj]
    calc ∫⁻ x, (ENNReal.ofReal (p * min x C) + valueToGo M k (Nat.le_of_succ_le hk) (C - min x C))
          ∂(M.μ ⟨N - (k + 1), by omega⟩ p)
        ≤ ∫⁻ x, (ENNReal.ofReal (p * x) + ∑ n ∈ Finset.univ.filter
            (fun n : Fin N => N - k ≤ n.val), ENNReal.ofReal (R n))
            ∂(M.μ ⟨N - (k + 1), by omega⟩ p) := by
          refine lintegral_mono fun x => add_le_add ?_ (ih _ _)
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hp')
      _ = ENNReal.ofReal (p * meanDemand M ⟨N - (k + 1), by omega⟩ p) + ∑ n ∈ Finset.univ.filter
            (fun n : Fin N => N - k ≤ n.val), ENNReal.ofReal (R n) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
          congr 1
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · congr 1; rw [integral_const_mul]; rfl
          · exact (M.integrable _ p).const_mul p
          · filter_upwards [M.nonneg ⟨N - (k + 1), by omega⟩ p] with x hx using mul_nonneg hp' hx
      _ ≤ _ := by gcongr; exact hR _ p hp'

/-- Scarf's bound on the expected overflow. -/
lemma scarf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) (C : ℝ) :
    ∫ ω, max (Y ω - C) 0 ∂P ≤
      (Real.sqrt (variance Y P + (C - ∫ ω, Y ω ∂P) ^ 2) - (C - ∫ ω, Y ω ∂P)) / 2 := by
  set Z : Ω → ℝ := fun ω => Y ω - C with hZdef
  have hZ : MemLp Z 2 P := hY.sub (memLp_const C)
  have hZi : Integrable Z P := hZ.integrable one_le_two
  have hAZ : MemLp (fun ω => |Z ω|) 2 P := hZ.abs
  have hEZ : ∫ ω, Z ω ∂P = ∫ ω, Y ω ∂P - C := by
    simp only [Z]
    rw [integral_sub (hY.integrable one_le_two) (integrable_const C)]
    simp
  have hVZ : variance Z P = variance Y P := variance_sub_const hY.aestronglyMeasurable C
  have h1 := variance_eq_sub hZ
  have h2 := variance_eq_sub hAZ
  have h3 := variance_nonneg (fun ω => |Z ω|) P
  have hsq : (fun ω => |Z ω|) ^ 2 = Z ^ 2 := by funext ω; simp [sq_abs]
  rw [hsq] at h2
  have hle : (∫ ω, |Z ω| ∂P) ^ 2 ≤ variance Y P + (C - ∫ ω, Y ω ∂P) ^ 2 := by
    have e : (C - ∫ ω, Y ω ∂P) ^ 2 = (∫ ω, Z ω ∂P) ^ 2 := by rw [hEZ]; ring
    rw [e, ← hVZ]
    linarith
  have habs : ∫ ω, |Z ω| ∂P ≤ Real.sqrt (variance Y P + (C - ∫ ω, Y ω ∂P) ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt hle)
  have hmax : ∀ ω, max (Y ω - C) 0 = (|Z ω| + Z ω) / 2 := by
    intro ω
    simp only [Z]
    rcases le_total 0 (Y ω - C) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  simp_rw [hmax]
  rw [integral_div, integral_add hZi.abs hZi, hEZ]
  linarith

section Prod

variable {N : ℕ} (M : PricingModel N) (pdet : Fin N → ℝ)

instance heurLaw_prob : IsProbabilityMeasure (heuristicLaw M pdet) := by
  unfold heuristicLaw; infer_instance

lemma mp_eval (i : Fin N) :
    MeasurePreserving (fun x : Fin N → ℝ => x i) (heuristicLaw M pdet) (M.μ i (pdet i)) :=
  measurePreserving_eval (fun n => M.μ n (pdet n)) i

lemma ae_nonneg : ∀ᵐ x ∂(heuristicLaw M pdet), ∀ i, 0 ≤ x i := by
  rw [ae_all_iff]
  intro i
  exact (mp_eval M pdet i).quasiMeasurePreserving.ae (M.nonneg i (pdet i))

lemma integrable_coord (i : Fin N) :
    Integrable (fun x : Fin N → ℝ => x i) (heuristicLaw M pdet) :=
  by
    unfold heuristicLaw
    exact integrable_comp_eval (μ := fun n => M.μ n (pdet n)) (i := i) (f := fun y : ℝ => y)
      (M.integrable i (pdet i))

lemma integral_coord (i : Fin N) :
    ∫ x, x i ∂(heuristicLaw M pdet) = meanDemand M i (pdet i) := by
  unfold heuristicLaw meanDemand
  exact integral_comp_eval (μ := fun n => M.μ n (pdet n)) (i := i) (f := fun y : ℝ => y)
    (by fun_prop)

/-- Resampling one coordinate of a product measure. -/
lemma resample (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f) (i : Fin N) :
    ∫⁻ x, f x ∂(heuristicLaw M pdet) =
      ∫⁻ x, ∫⁻ t, f (Function.update x i t) ∂(M.μ i (pdet i)) ∂(heuristicLaw M pdet) := by
  unfold heuristicLaw
  have hg : Measurable (∫⋯∫⁻_{i}, f ∂(fun n => M.μ n (pdet n))) := hf.lmarginal _
  have hsing := lmarginal_singleton (μ := fun n => M.μ n (pdet n)) f i
  rw [← hsing, lintegral_eq_lmarginal_univ 0, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' f hf (Finset.mem_univ i), lmarginal_erase' _ hg (Finset.mem_univ i)]
  congr 1
  funext x
  simp only [lmarginal_update_of_mem (fun n => M.μ n (pdet n)) (Finset.mem_singleton_self i),
    lintegral_const, measure_univ, mul_one]
  exact (congrFun hsing x).symm

end Prod

/-- Sales of period `n` under the fixed prices, with demands clipped at `0`. -/
noncomputable def sales {N : ℕ} (C : ℝ) (x : Fin N → ℝ) (n : Fin N) : ℝ :=
  min (max (x n) 0) (max (C - ∑ i ∈ Finset.univ.filter (fun i => i < n), max (x i) 0) 0)

/-- Fixed-price revenue of the last `k` periods, from inventory `C`. -/
noncomputable def G {N : ℕ} (pdet : Fin N → ℝ) (k : ℕ) (C : ℝ) (x : Fin N → ℝ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.univ.filter (fun n : Fin N => N - k ≤ n.val),
    ENNReal.ofReal (pdet n * min (max (x n) 0)
      (max (C - ∑ i ∈ Finset.univ.filter (fun i : Fin N => N - k ≤ i.val ∧ i < n),
        max (x i) 0) 0))

lemma sales_nonneg {N : ℕ} (C : ℝ) (x : Fin N → ℝ) (n : Fin N) : 0 ≤ sales C x n :=
  le_min (le_max_right _ _) (le_max_right _ _)

lemma G_measurable {N : ℕ} (pdet : Fin N → ℝ) (k : ℕ) :
    Measurable (fun q : ℝ × (Fin N → ℝ) => G pdet k q.1 q.2) := by
  unfold G
  refine Finset.measurable_sum _ fun n _ => ?_
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.const_mul ?_ _
  refine Measurable.min ?_ ?_
  · exact (measurable_pi_apply n).comp measurable_snd |>.max measurable_const
  · refine Measurable.max ?_ measurable_const
    refine measurable_fst.sub ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_pi_apply i).comp measurable_snd |>.max measurable_const

lemma G_zero {N : ℕ} (pdet : Fin N → ℝ) (C : ℝ) (x : Fin N → ℝ) : G pdet 0 C x = 0 := by
  unfold G
  have : Finset.univ.filter (fun n : Fin N => N - 0 ≤ n.val) = ∅ := by
    ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_le]; have := n.isLt; omega
  rw [this, Finset.sum_empty]

lemma G_step {N : ℕ} (pdet : Fin N → ℝ) (k : ℕ) (hk : k + 1 ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (j : Fin N) (hjv : j.val = N - (k + 1)) (x : Fin N → ℝ) (y : ℝ) :
    G pdet (k + 1) C (Function.update x j y) =
      ENNReal.ofReal (pdet j * min (max y 0) C) +
        G pdet k (C - min (max y 0) C) x := by
  unfold G
  have hsplit : Finset.univ.filter (fun n : Fin N => N - (k + 1) ≤ n.val) =
      insert j (Finset.univ.filter (fun n : Fin N => N - k ≤ n.val)) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff, hjv]; omega
  have hj : j ∉ Finset.univ.filter (fun n : Fin N => N - k ≤ n.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hjv]; omega
  rw [hsplit, Finset.sum_insert hj]
  congr 1
  · -- the first period
    have hempty : Finset.univ.filter (fun i : Fin N => N - (k + 1) ≤ i.val ∧ i < j) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and, not_lt, Fin.le_iff_val_le_val, hjv]; omega
    rw [hempty, Finset.sum_empty, Function.update_self, sub_zero, max_eq_left hC]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    have hnj : n ≠ j := by intro h; rw [h, hjv] at hn; omega
    have hsplit2 : Finset.univ.filter (fun i : Fin N => N - (k + 1) ≤ i.val ∧ i < n) =
        insert j (Finset.univ.filter (fun i : Fin N => N - k ≤ i.val ∧ i < n)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, Fin.lt_def, hjv]; omega
    have hj2 : j ∉ Finset.univ.filter (fun i : Fin N => N - k ≤ i.val ∧ i < n) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, Fin.lt_def, hjv]; omega
    rw [hsplit2, Finset.sum_insert hj2, Function.update_self, Function.update_of_ne hnj]
    have hrest : ∑ i ∈ Finset.univ.filter (fun i : Fin N => N - k ≤ i.val ∧ i < n),
        max (Function.update x j y i) 0 =
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => N - k ≤ i.val ∧ i < n), max (x i) 0 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i ≠ j := by
        intro h; rw [h] at hi; exact hj2 hi
      rw [Function.update_of_ne hij]
    rw [hrest]
    set S := ∑ i ∈ Finset.univ.filter (fun i : Fin N => N - k ≤ i.val ∧ i < n), max (x i) 0
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => le_max_right _ _
    have hy : 0 ≤ max y 0 := le_max_right _ _
    have key : max (C - (max y 0 + S)) 0 = max (C - min (max y 0) C - S) 0 := by
      rcases le_total (max y 0) C with h | h
      · rw [min_eq_left h]; congr 1; ring
      · rw [min_eq_right h, sub_self, zero_sub,
          max_eq_right (by linarith : C - (max y 0 + S) ≤ 0), max_eq_right (by linarith : -S ≤ 0)]
    rw [key]

lemma G_le_value {N : ℕ} (M : PricingModel N) (pdet : Fin N → ℝ) (hpos : ∀ n, 0 ≤ pdet n) :
    ∀ (k : ℕ) (hk : k ≤ N) (C : ℝ), 0 ≤ C →
      ∫⁻ x, G pdet k C x ∂(heuristicLaw M pdet) ≤ valueToGo M k hk C := by
  intro k
  induction k with
  | zero =>
    intro hk C hC
    simp [G_zero]
  | succ k ih =>
    intro hk C hC
    obtain ⟨j, hjv⟩ : ∃ j : Fin N, j.val = N - (k + 1) := ⟨⟨N - (k + 1), by omega⟩, rfl⟩
    have hjeq : (⟨N - (k + 1), by omega⟩ : Fin N) = j := Fin.ext hjv.symm
    have hGm : ∀ c, Measurable (fun x => G pdet (k + 1) c x) := fun c =>
      (G_measurable pdet (k + 1)).comp (measurable_const.prodMk measurable_id)
    rw [resample M pdet _ (hGm C) j]
    simp_rw [G_step pdet k hk C hC j hjv]
    have hjoint : Measurable (Function.uncurry fun (x : Fin N → ℝ) (y : ℝ) =>
        ENNReal.ofReal (pdet j * min (max y 0) C) + G pdet k (C - min (max y 0) C) x) := by
      show Measurable (fun q : (Fin N → ℝ) × ℝ => ENNReal.ofReal (pdet j * min (max q.2 0) C) +
        G pdet k (C - min (max q.2 0) C) q.1)
      have hA : Measurable (fun q : (Fin N → ℝ) × ℝ =>
          ENNReal.ofReal (pdet j * min (max q.2 0) C)) :=
        ENNReal.measurable_ofReal.comp
          ((measurable_snd.max measurable_const).min measurable_const |>.const_mul _)
      have hB : Measurable (fun q : (Fin N → ℝ) × ℝ => G pdet k (C - min (max q.2 0) C) q.1) :=
        (G_measurable pdet k).comp
          ((measurable_const.sub ((measurable_snd.max measurable_const).min measurable_const)).prodMk
            measurable_fst)
      exact hA.add hB
    rw [lintegral_lintegral_swap hjoint.aemeasurable]
    rw [valueToGo, hjeq]
    refine le_trans ?_ (le_iSup₂ (f := fun p (_ : p ∈ Set.Ici (0:ℝ)) => ∫⁻ x,
      (ENNReal.ofReal (p * min x C) + valueToGo M k (Nat.le_of_succ_le hk) (C - min x C))
        ∂(M.μ j p)) (pdet j) (Set.mem_Ici.mpr (hpos j)))
    refine lintegral_mono_ae ?_
    filter_upwards [M.nonneg j (pdet j)] with y hy
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    rw [max_eq_left hy]
    gcongr
    exact ih _ _ (by
      rcases le_total y C with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith)

end PricingRM.DetHeuristic.P21cc

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic in
theorem solution {N : ℕ} (M : PricingModel N) (hN : 0 < N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    (C₀ : ℝ) (hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand M n pinf < C₀)
    (pdet : Fin N → ℝ) (hopt : IsDetOptimal M C₀ pdet)
    (hL2 : ∀ n, MemLp (fun x : ℝ => x) 2 (M.μ n (pdet n)))
    (hmean : ∀ n, 0 < meanDemand M n (pdet n))
    (hVdet : 0 < detObjective M pdet) :
    1 ≥ heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ∧
      heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ≥
        (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ∧
      (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ≥
        1 - Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun n => eta M C₀ pdet n / meanDemand M n (pdet n)) := by
  open PricingRM.DetHeuristic.P21cc in
  classical
  set V := detObjective M pdet with hVdef
  set H := heuristicRevenue M C₀ pdet with hHdef
  set O := optValue M C₀ with hOdef
  have hpos : ∀ n, 0 ≤ pdet n := hopt.1.1
  have hC₀ : 0 ≤ C₀ := by
    obtain ⟨pinf, -, h⟩ := hslater
    have := Finset.sum_nonneg fun n (_ : n ∈ Finset.univ) => meanDemand_nonneg M n pinf
    linarith
  -- the revenue as a sum of clipped sales
  have hsales_int : ∀ n, Integrable (fun x => sales C₀ x n) (heuristicLaw M pdet) := by
    intro n
    refine Integrable.mono' (integrable_coord M pdet n).abs ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      unfold sales
      refine Measurable.min ((measurable_pi_apply n).max measurable_const) ?_
      refine Measurable.max ?_ measurable_const
      refine measurable_const.sub ?_
      exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).max measurable_const
    · refine Filter.Eventually.of_forall fun x => ?_
      unfold sales
      have h0 : 0 ≤ min (max (x n) 0)
          (max (C₀ - ∑ i ∈ Finset.univ.filter (fun i => i < n), max (x i) 0) 0) :=
        le_min (le_max_right _ _) (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      refine le_trans (min_le_left _ _) ?_
      rcases le_total 0 (x n) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]
      · rw [max_eq_right h]; exact abs_nonneg _
  have hH : H = ∑ n, pdet n * ∫ x, sales C₀ x n ∂(heuristicLaw M pdet) := by
    rw [hHdef, heuristicRevenue]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg M pdet] with x hx
    simp only [sales, cumDemandBefore]
    rw [max_eq_left (hx n)]
    have hs : ∑ i ∈ Finset.univ.filter (fun i => i < n), max (x i) 0
        = ∑ i ∈ Finset.univ.filter (fun i => i < n), x i :=
      Finset.sum_congr rfl fun i _ => max_eq_left (hx i)
    rw [hs]
    set a := max (C₀ - ∑ i ∈ Finset.univ.filter (fun i => i < n), x i) 0
    rcases le_total (x n) a with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hH0 : 0 ≤ H := by
    rw [hH]
    refine Finset.sum_nonneg fun n _ => mul_nonneg (hpos n) (integral_nonneg fun x => ?_)
    exact le_min (le_max_right _ _) (le_max_right _ _)
  -- lower bound on each period's sales
  have hsales_lb : ∀ n, meanDemand M n (pdet n) - eta M C₀ pdet n ≤ ∫ x, sales C₀ x n ∂(heuristicLaw M pdet) := by
    intro n
    have hY : MemLp (fun x => cumDemand x n) 2 (heuristicLaw M pdet) := by
      unfold cumDemand
      refine memLp_finsetSum _ fun i _ => ?_
      exact (hL2 i).comp_measurePreserving (mp_eval M pdet i)
    have hsc := scarf (heuristicLaw M pdet) (fun x => cumDemand x n) hY C₀
    have hYi : Integrable (fun x => max (cumDemand x n - C₀) 0) (heuristicLaw M pdet) :=
      ((hY.integrable one_le_two).sub (integrable_const C₀)).pos_part
    have hmono : ∫ x, (x n - max (cumDemand x n - C₀) 0) ∂(heuristicLaw M pdet) ≤ ∫ x, sales C₀ x n ∂(heuristicLaw M pdet) := by
      refine integral_mono_ae ((integrable_coord M pdet n).sub hYi) (hsales_int n) ?_
      filter_upwards [ae_nonneg M pdet] with x hx
      have hcd : cumDemand x n = cumDemandBefore x n + x n := by
        unfold cumDemand cumDemandBefore
        have : Finset.univ.filter (fun i => i ≤ n) =
            insert n (Finset.univ.filter (fun i => i < n)) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact le_iff_eq_or_lt
        rw [this, Finset.sum_insert (by simp), add_comm]
      simp only [sales]
      rw [max_eq_left (hx n)]
      have hs : ∑ i ∈ Finset.univ.filter (fun i => i < n), max (x i) 0 = cumDemandBefore x n :=
        Finset.sum_congr rfl fun i _ => max_eq_left (hx i)
      rw [hs, hcd]
      set B := cumDemandBefore x n
      rcases le_total 0 (C₀ - B) with h | h
      · rw [max_eq_left h]
        rcases le_total (x n) (C₀ - B) with h' | h'
        · rw [min_eq_left h', max_eq_right (by linarith)]; linarith
        · rw [min_eq_right h', max_eq_left (by linarith)]; linarith
      · rw [max_eq_right h, min_eq_right (hx n)]
        have : B + x n - C₀ ≤ max (B + x n - C₀) 0 := le_max_left _ _
        linarith
    rw [integral_sub (integrable_coord M pdet n) hYi, integral_coord] at hmono
    have heta : eta M C₀ pdet n = (Real.sqrt (variance (fun x => cumDemand x n) (heuristicLaw M pdet) +
        (C₀ - ∫ x, cumDemand x n ∂(heuristicLaw M pdet)) ^ 2) - (C₀ - ∫ x, cumDemand x n ∂(heuristicLaw M pdet))) / 2 := rfl
    linarith
  -- the DP bounds
  have hR : ∀ n p, 0 ≤ p → p * meanDemand M n p ≤ pdet n * meanDemand M n (pdet n) :=
    fun n p hp => rev_le_opt M hconc hconv hopt n hp
  have hOup : O ≤ ENNReal.ofReal V := by
    have h := value_le M (fun n => pdet n * meanDemand M n (pdet n)) hR N le_rfl C₀
    have hf : Finset.univ.filter (fun n : Fin N => N - N ≤ n.val) = Finset.univ := by
      ext n; simp
    rw [hf, ← ENNReal.ofReal_sum_of_nonneg fun n _ =>
      mul_nonneg (hpos n) (meanDemand_nonneg M n (pdet n))] at h
    exact h
  have hOlow : ENNReal.ofReal H ≤ O := by
    have h := G_le_value M pdet hpos N le_rfl C₀ hC₀
    have hG : ∀ x, G pdet N C₀ x = ∑ n, ENNReal.ofReal (pdet n * sales C₀ x n) := by
      intro x
      unfold G sales
      have hf : Finset.univ.filter (fun n : Fin N => N - N ≤ n.val) = Finset.univ := by
        ext n; simp
      rw [hf]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hf2 : Finset.univ.filter (fun i : Fin N => N - N ≤ i.val ∧ i < n) =
          Finset.univ.filter (fun i : Fin N => i < n) := by
        ext i; simp
      rw [hf2]
    simp_rw [hG] at h
    rw [lintegral_finsetSum] at h
    · have hterm : ∀ n, ∫⁻ x, ENNReal.ofReal (pdet n * sales C₀ x n) ∂(heuristicLaw M pdet) =
          ENNReal.ofReal (pdet n * ∫ x, sales C₀ x n ∂(heuristicLaw M pdet)) := by
        intro n
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
        · exact (hsales_int n).const_mul _
        · exact Filter.Eventually.of_forall fun x =>
            mul_nonneg (hpos n) (le_min (le_max_right _ _) (le_max_right _ _))
      simp_rw [hterm] at h
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun n => pdet n * ∫ x, sales C₀ x n ∂(heuristicLaw M pdet))
        (fun n _ => mul_nonneg (hpos n) (integral_nonneg fun x => sales_nonneg C₀ x n)),
        ← hH] at h
      exact h
    · intro n _
      refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
      unfold sales
      refine Measurable.min ((measurable_pi_apply n).max measurable_const) ?_
      refine Measurable.max ?_ measurable_const
      refine measurable_const.sub ?_
      exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).max measurable_const
  have hOtop : O ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hOup
  have hOV : O.toReal ≤ V := by
    rw [← ENNReal.toReal_ofReal hVdet.le]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hOup
  have hHO : H ≤ O.toReal := (ENNReal.ofReal_le_iff_le_toReal hOtop).mp hOlow
  have hO0 : 0 ≤ O.toReal := ENNReal.toReal_nonneg
  -- the middle bound
  set L := ∑ n, pdet n * meanDemand M n (pdet n) * (1 - eta M C₀ pdet n / meanDemand M n (pdet n))
    with hLdef
  have hLH : L ≤ H := by
    rw [hLdef, hH]
    refine Finset.sum_le_sum fun n _ => ?_
    have hm := hmean n
    have e : pdet n * meanDemand M n (pdet n) * (1 - eta M C₀ pdet n / meanDemand M n (pdet n))
        = pdet n * (meanDemand M n (pdet n) - eta M C₀ pdet n) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hsales_lb n) (hpos n)
  refine ⟨?_, ?_, ?_⟩
  · -- ratio ≤ 1
    show H / O.toReal ≤ 1
    rcases eq_or_lt_of_le hO0 with h | h
    · rw [← h, div_zero]; norm_num
    · exact (div_le_one h).mpr hHO
  · show 1 / V * L ≤ H / O.toReal
    rcases le_or_gt L 0 with hL | hL
    · have : 1 / V * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hL
      exact le_trans this (div_nonneg hH0 hO0)
    · have hHpos : 0 < H := lt_of_lt_of_le hL hLH
      have hOpos : 0 < O.toReal := lt_of_lt_of_le hHpos hHO
      calc 1 / V * L = L / V := by ring
        _ ≤ H / V := div_le_div_of_nonneg_right hLH hVdet.le
        _ ≤ H / O.toReal := div_le_div_of_nonneg_left hH0 hOpos hOV
  · show 1 - Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun n => eta M C₀ pdet n / meanDemand M n (pdet n)) ≤ 1 / V * L
    set S := Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun n => eta M C₀ pdet n / meanDemand M n (pdet n)) with hSdef
    have hsum : (1 - S) * V ≤ L := by
      rw [hVdef, detObjective, Finset.mul_sum, hLdef]
      refine Finset.sum_le_sum fun n _ => ?_
      have hle : eta M C₀ pdet n / meanDemand M n (pdet n) ≤ S :=
        Finset.le_sup' (fun n => eta M C₀ pdet n / meanDemand M n (pdet n)) (Finset.mem_univ n)
      have hr : 0 ≤ pdet n * meanDemand M n (pdet n) :=
        mul_nonneg (hpos n) (hmean n).le
      nlinarith
    rw [one_div_mul_eq_div, le_div_iff₀ hVdet]
    exact hsum
