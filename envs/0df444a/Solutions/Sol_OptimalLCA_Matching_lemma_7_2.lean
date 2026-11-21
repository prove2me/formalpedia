-- Prove2me | solution 1 for OptimalLCA.Matching.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:26:06.536183+00:00
-- url     : https://prove2.me/submissions/20d0c792-3f99-44b3-ba2a-7167f8a9fe67

import Mathlib

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 4000000

theorem solution {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (m : ℕ) (X : Fin m → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hind : iIndepFun X)
    (K : ℕ) (hK : 1 ≤ K) (ℓ : ℝ) (hmean : ∫ ω, ∑ i, X i ω = (K : ℝ) * ℓ) :
    (1 - 2 / Real.sqrt K) * min 1 ℓ ≤ (∫ ω, min (K : ℝ) (∑ i, X i ω)) / K ∧
      (∫ ω, min (K : ℝ) (∑ i, X i ω)) / K ≤ min 1 ℓ := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hsqrtK_pos : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKpos
  -- the sum N
  set N : Ω → ℝ := fun ω => ∑ i, X i ω with hNdef
  have hNmeas : Measurable N := by
    have h := Finset.measurable_sum (Finset.univ : Finset (Fin m)) (fun i _ => hXm i)
    simpa [hNdef] using h
  have hN_nonneg : ∀ ω, 0 ≤ N ω := by
    intro ω; rw [hNdef]
    exact Finset.sum_nonneg (fun i _ => by rcases hX01 i ω with h | h <;> simp [h])
  have hN_le : ∀ ω, N ω ≤ (m : ℝ) := by
    intro ω; rw [hNdef]
    calc ∑ i, X i ω ≤ ∑ _i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => by rcases hX01 i ω with h | h <;> simp [h])
      _ = (m : ℝ) := by simp
  -- integrability toolkit
  have int_of_bound : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ C) → Integrable f := by
    intro f C hf hC
    exact (MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).integrable (q := 2) (by norm_num)
  have hXi_memLp : ∀ i, MemLp (X i) 2 (volume : Measure Ω) := fun i =>
    memLp_of_bounded (a := 0) (b := 1) (Filter.Eventually.of_forall (fun ω => by
      rcases hX01 i ω with h | h <;> simp [h])) (hXm i).aestronglyMeasurable 2
  have hXi_int : ∀ i, Integrable (X i) := fun i =>
    (hXi_memLp i).integrable (q := 2) (by norm_num)
  have hN_int : Integrable N :=
    int_of_bound N (m : ℝ) hNmeas (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hN_nonneg ω)]; exact hN_le ω)
  -- the mean S
  set S : ℝ := ∫ ω, N ω with hSdef
  have hS_eq : S = (K : ℝ) * ℓ := by
    rw [hSdef, hNdef]
    exact hmean
  have hℓ_nonneg : 0 ≤ ℓ := by
    have h1 : 0 ≤ S := by rw [hSdef]; exact integral_nonneg hN_nonneg
    rw [hS_eq] at h1
    nlinarith
  -- variance
  set V : ℝ := variance N (volume : Measure Ω) with hVdef
  have hV_eq : V = ∫ ω, (N ω - S) ^ 2 := by
    rw [hVdef, hSdef]
    exact variance_eq_integral hNmeas.aemeasurable
  have hsum_fun : (∑ i, X i) = N := by
    rw [hNdef]; funext ω; exact Finset.sum_apply ω _ _
  have hV_le : V ≤ (K : ℝ) * ℓ := by
    rw [hVdef]
    have hvar_sum : variance N (volume : Measure Ω) =
        ∑ i, variance (X i) (volume : Measure Ω) := by
      rw [← hsum_fun]
      exact IndepFun.variance_sum (μ := (volume : Measure Ω)) (s := Finset.univ) (X := X)
        (fun i _ => hXi_memLp i) (fun i _ j _ hij => hind.indepFun hij)
    rw [hvar_sum]
    calc ∑ i, variance (X i) (volume : Measure Ω) ≤ ∑ i, ∫ ω, X i ω := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h := variance_eq_sub (hXi_memLp i)
          rw [h]
          have hsq : ∫ ω, (X i ω) ^ 2 = ∫ ω, X i ω := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            rcases hX01 i ω with h | h <;> simp [h]
          simp only [Pi.pow_apply]
          rw [hsq]
          linarith [sq_nonneg (∫ ω, X i ω)]
      _ = ∫ ω, ∑ i, X i ω := by
          rw [integral_finsetSum (s := Finset.univ) (f := X) (fun i _ => hXi_int i)]
      _ = (K : ℝ) * ℓ := hmean
  -- the key truncated quantity A and companions
  set A : ℝ := ∫ ω, max 0 (N ω - (K : ℝ)) with hAdef
  set B : ℝ := ∫ ω, max 0 ((K : ℝ) - N ω) with hBdef
  set Ab : ℝ := ∫ ω, |N ω - S| with hAbdef
  have hA_int : Integrable (fun ω => max 0 (N ω - (K : ℝ))) :=
    int_of_bound _ (m : ℝ) (measurable_const.max (hNmeas.sub measurable_const)) (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
      exact max_le (by positivity) (by linarith [hN_le ω, hKpos.le]))
  have hB_int : Integrable (fun ω => max 0 ((K : ℝ) - N ω)) :=
    int_of_bound _ (K : ℝ) (measurable_const.max (measurable_const.sub hNmeas)) (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
      exact max_le hKpos.le (by linarith [hN_nonneg ω]))
  have hAbs_bound : ∀ ω, |N ω - S| ≤ (m : ℝ) + |S| := by
    intro ω
    calc |N ω - S| ≤ |N ω| + |S| := abs_sub _ _
      _ = N ω + |S| := by rw [abs_of_nonneg (hN_nonneg ω)]
      _ ≤ (m : ℝ) + |S| := by linarith [hN_le ω]
  have hSq_int : Integrable (fun ω => (N ω - S) ^ 2) :=
    int_of_bound _ (((m : ℝ) + |S|) ^ 2) ((hNmeas.sub measurable_const).pow_const 2) (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hAbs_bound ω) 2)
  have hAbs_int : Integrable (fun ω => |N ω - S|) :=
    int_of_bound _ ((m : ℝ) + |S|) ((hNmeas.sub measurable_const).abs) (fun ω => by
      rw [Real.norm_eq_abs, abs_abs]; exact hAbs_bound ω)
  -- pointwise comparisons
  have hA_le_Ab : S ≤ (K : ℝ) → A ≤ Ab := by
    intro hSK
    rw [hAdef, hAbdef]
    refine integral_mono hA_int hAbs_int (fun ω => ?_)
    rcases le_or_gt (N ω) (K : ℝ) with h | h
    · rw [max_eq_left (by linarith : N ω - (K : ℝ) ≤ 0)]
      exact abs_nonneg (N ω - S)
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ N ω - (K : ℝ)),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ N ω - S)]
      linarith
  have hB_le_Ab : (K : ℝ) ≤ S → B ≤ Ab := by
    intro hKS
    rw [hBdef, hAbdef]
    refine integral_mono hB_int hAbs_int (fun ω => ?_)
    rcases le_or_gt (N ω) (K : ℝ) with h | h
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ (K : ℝ) - N ω)]
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ S - N ω)]
      linarith
    · rw [max_eq_left (by linarith : (K : ℝ) - N ω ≤ 0)]
      exact abs_nonneg (N ω - S)
  have hA_exact : A = (S - (K : ℝ)) + B := by
    have hpt : ∀ ω, N ω - (K : ℝ) = max 0 (N ω - (K : ℝ)) - max 0 ((K : ℝ) - N ω) := by
      intro ω
      rcases le_or_gt (N ω) (K : ℝ) with h | h
      · rw [max_eq_left (by linarith : N ω - (K : ℝ) ≤ 0),
            max_eq_right (by linarith : (0 : ℝ) ≤ (K : ℝ) - N ω)]; ring
      · rw [max_eq_right (by linarith : (0 : ℝ) ≤ N ω - (K : ℝ)),
            max_eq_left (by linarith : (K : ℝ) - N ω ≤ 0)]; ring
    have h1 : ∫ ω, (N ω - (K : ℝ)) = A - B := by
      rw [hAdef, hBdef, ← integral_sub hA_int hB_int]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    have h2 : ∫ ω, (N ω - (K : ℝ)) = S - (K : ℝ) := by
      rw [integral_sub hN_int (integrable_const (K : ℝ)), ← hSdef]
      simp
    linarith
  have hA_sq : S < (K : ℝ) → A ≤ V / ((K : ℝ) - S) := by
    intro hSK
    have hden : 0 < (K : ℝ) - S := by linarith
    have hmain : A ≤ ∫ ω, (N ω - S) ^ 2 / ((K : ℝ) - S) := by
      rw [hAdef]
      refine integral_mono hA_int (hSq_int.div_const _) (fun ω => ?_)
      rcases le_or_gt (N ω) (K : ℝ) with h | h
      · rw [max_eq_left (by linarith : N ω - (K : ℝ) ≤ 0)]; positivity
      · rw [max_eq_right (by linarith : (0 : ℝ) ≤ N ω - (K : ℝ)), le_div_iff₀ hden]
        nlinarith [h, hSK]
    calc A ≤ ∫ ω, (N ω - S) ^ 2 / ((K : ℝ) - S) := hmain
      _ = V / ((K : ℝ) - S) := by rw [integral_div, hV_eq]
  have hB_sq : (K : ℝ) < S → B ≤ V / (S - (K : ℝ)) := by
    intro hKS
    have hden : 0 < S - (K : ℝ) := by linarith
    have hmain : B ≤ ∫ ω, (N ω - S) ^ 2 / (S - (K : ℝ)) := by
      rw [hBdef]
      refine integral_mono hB_int (hSq_int.div_const _) (fun ω => ?_)
      rcases le_or_gt (N ω) (K : ℝ) with h | h
      · rw [max_eq_right (by linarith : (0 : ℝ) ≤ (K : ℝ) - N ω), le_div_iff₀ hden]
        nlinarith [h, hKS]
      · rw [max_eq_left (by linarith : (K : ℝ) - N ω ≤ 0)]; positivity
    calc B ≤ ∫ ω, (N ω - S) ^ 2 / (S - (K : ℝ)) := hmain
      _ = V / (S - (K : ℝ)) := by rw [integral_div, hV_eq]
  have hAb_bound : ∀ t : ℝ, 0 < t → Ab ≤ t / 2 + V / (2 * t) := by
    intro t ht
    have hpt : ∀ ω, |N ω - S| ≤ t / 2 + (N ω - S) ^ 2 / (2 * t) := by
      intro ω
      have hkey : t / 2 + (N ω - S) ^ 2 / (2 * t) = (t ^ 2 + (N ω - S) ^ 2) / (2 * t) := by
        field_simp
      rw [hkey, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
      nlinarith [sq_nonneg (|N ω - S| - t), sq_abs (N ω - S), abs_nonneg (N ω - S)]
    calc Ab = ∫ ω, |N ω - S| := hAbdef
      _ ≤ ∫ ω, (t / 2 + (N ω - S) ^ 2 / (2 * t)) :=
          integral_mono hAbs_int
            ((integrable_const (t / 2)).add (hSq_int.div_const (2 * t))) hpt
      _ = t / 2 + (∫ ω, (N ω - S) ^ 2) / (2 * t) := by
          rw [integral_add (integrable_const (t / 2)) (hSq_int.div_const (2 * t))]
          have hc : ∫ (_x : Ω), t / 2 ∂volume = t / 2 := by simp
          rw [hc]
          exact congrArg (fun z => t / 2 + z) (integral_div (2 * t) (fun ω => (N ω - S) ^ 2))
      _ = t / 2 + V / (2 * t) := by rw [← hV_eq]
  -- integral of the clipped min
  have hmin_id : ∀ ω, min (K : ℝ) (N ω) = N ω - max 0 (N ω - (K : ℝ)) := by
    intro ω
    rcases le_or_gt (N ω) (K : ℝ) with h | h
    · rw [min_eq_right h, max_eq_left (by linarith : N ω - (K : ℝ) ≤ 0)]; ring
    · rw [min_eq_left h.le, max_eq_right (by linarith : (0 : ℝ) ≤ N ω - (K : ℝ))]; ring
  have hmin_int : Integrable (fun ω => min (K : ℝ) (N ω)) :=
    int_of_bound _ (K : ℝ) (measurable_const.min hNmeas) (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hKpos.le (hN_nonneg ω))]
      exact min_le_left _ _)
  have hMin_eq : ∫ ω, min (K : ℝ) (N ω) = (K : ℝ) * ℓ - A := by
    have h1 : ∫ ω, min (K : ℝ) (N ω) = ∫ ω, (N ω - max 0 (N ω - (K : ℝ))) :=
      integral_congr_ae (Filter.Eventually.of_forall hmin_id)
    rw [h1, integral_sub hN_int hA_int, ← hS_eq, hAdef]
  -- bound on A in all cases
  have hA_bound : A ≤ (K : ℝ) * ℓ - (K : ℝ) * min 1 ℓ + 2 * Real.sqrt (K : ℝ) * min 1 ℓ := by
    rcases le_or_gt ℓ 1 with hℓ1 | hℓ1
    · -- ℓ ≤ 1
      have hminl : min 1 ℓ = ℓ := min_eq_right hℓ1
      rw [hminl]
      have hzero : (K : ℝ) * ℓ - (K : ℝ) * ℓ + 2 * Real.sqrt (K : ℝ) * ℓ
          = 2 * Real.sqrt (K : ℝ) * ℓ := by ring
      rw [hzero]
      rcases le_or_gt (1 / 4 : ℝ) ℓ with hq | hq
      · -- 1/4 ≤ ℓ ≤ 1
        have hSpos : 0 < S := by rw [hS_eq]; nlinarith only [hKpos, hq]
        have h1 : A ≤ Ab := hA_le_Ab (by rw [hS_eq]; nlinarith only [hKpos, hℓ1])
        have h2 : Ab ≤ Real.sqrt S := by
          have h := hAb_bound (Real.sqrt S) (Real.sqrt_pos.mpr hSpos)
          have hVS : V ≤ S := by rw [hS_eq]; exact hV_le
          have hsq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hSpos.le
          have hVb : V / (2 * Real.sqrt S) ≤ Real.sqrt S / 2 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt S)]
            nlinarith only [hVS, hsq]
          linarith
        have h3 : Real.sqrt S ≤ 2 * Real.sqrt (K : ℝ) * ℓ := by
          rw [hS_eq, Real.sqrt_mul hKpos.le]
          have hℓpos : 0 < ℓ := by linarith
          have hs1 : Real.sqrt ℓ ≤ 2 * ℓ := by
            rw [Real.sqrt_le_left (by linarith)]
            nlinarith only [hq]
          have hs2 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
          nlinarith only [hs1, hs2]
        linarith
      · -- ℓ ≤ 1/4
        have hSK : S < (K : ℝ) := by rw [hS_eq]; nlinarith only [hKpos, hq]
        have hden : 0 < (K : ℝ) - S := by linarith
        have h1 : A ≤ V / ((K : ℝ) - S) := hA_sq hSK
        have h2 : V / ((K : ℝ) - S) ≤ ℓ / (1 - ℓ) := by
          rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ℓ)]
          nlinarith only [hV_le, hS_eq, hKpos, hq]
        have h3 : ℓ / (1 - ℓ) ≤ 2 * ℓ := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ℓ)]
          nlinarith only [hℓ_nonneg, hq]
        have h4 : 2 * ℓ ≤ 2 * Real.sqrt (K : ℝ) * ℓ := by
          have hs : 1 ≤ Real.sqrt (K : ℝ) := by
            rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hK)
          nlinarith only [hℓ_nonneg, hs]
        linarith
    · -- 1 < ℓ
      have hminl : min 1 ℓ = 1 := min_eq_left hℓ1.le
      rw [hminl, mul_one]
      have hArep : A = ((K : ℝ) * ℓ - (K : ℝ)) + B := by
        rw [hA_exact, hS_eq]
      rw [hArep]
      rcases le_or_gt ℓ 4 with h4 | h4
      · -- 1 < ℓ ≤ 4
        have h1 : B ≤ Ab := hB_le_Ab (by rw [hS_eq]; nlinarith only [hKpos, hℓ1])
        have h2 : Ab ≤ 2 * Real.sqrt (K : ℝ) := by
          have h := hAb_bound (2 * Real.sqrt (K : ℝ)) (by positivity)
          have hstep : V / (2 * (2 * Real.sqrt (K : ℝ))) ≤ Real.sqrt (K : ℝ) := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * Real.sqrt (K : ℝ)))]
            have hsq : Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) :=
              Real.mul_self_sqrt hKpos.le
            nlinarith only [hV_le, hKpos, h4, hsq]
          linarith
        linarith
      · -- ℓ ≥ 4
        have hKS : (K : ℝ) < S := by rw [hS_eq]; nlinarith only [hKpos, h4]
        have h1 : B ≤ V / (S - (K : ℝ)) := hB_sq hKS
        have h2 : V / (S - (K : ℝ)) ≤ 2 := by
          rw [hS_eq, div_le_iff₀ (by nlinarith only [hKpos, h4] :
            (0 : ℝ) < (K : ℝ) * ℓ - (K : ℝ))]
          nlinarith only [hV_le, hKpos, h4]
        have h3 : (2 : ℝ) ≤ 2 * Real.sqrt (K : ℝ) := by
          have hs : 1 ≤ Real.sqrt (K : ℝ) := by
            rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hK)
          linarith
        linarith
  refine ⟨?_, ?_⟩
  · -- lower bound
    rw [hMin_eq, le_div_iff₀ hKpos]
    have hkey : (1 - 2 / Real.sqrt (K : ℝ)) * min 1 ℓ * (K : ℝ)
        = (K : ℝ) * min 1 ℓ - 2 * Real.sqrt (K : ℝ) * min 1 ℓ := by
      have hs : Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) := Real.mul_self_sqrt hKpos.le
      have hdiv : (2 : ℝ) / Real.sqrt (K : ℝ) * (K : ℝ) = 2 * Real.sqrt (K : ℝ) := by
        rw [div_mul_eq_mul_div, div_eq_iff hsqrtK_pos.ne']
        nlinarith only [hs]
      calc (1 - 2 / Real.sqrt (K : ℝ)) * min 1 ℓ * (K : ℝ)
          = min 1 ℓ * (K : ℝ) - min 1 ℓ * ((2 : ℝ) / Real.sqrt (K : ℝ) * (K : ℝ)) := by ring
        _ = min 1 ℓ * (K : ℝ) - min 1 ℓ * (2 * Real.sqrt (K : ℝ)) := by rw [hdiv]
        _ = (K : ℝ) * min 1 ℓ - 2 * Real.sqrt (K : ℝ) * min 1 ℓ := by ring
    rw [hkey]
    linarith
  · -- upper bound
    rw [div_le_iff₀ hKpos]
    have hmin : min 1 ℓ * (K : ℝ) = min (K : ℝ) ((K : ℝ) * ℓ) := by
      rw [mul_comm (min 1 ℓ) (K : ℝ), mul_min_of_nonneg 1 ℓ hKpos.le, mul_one]
    rw [hmin]
    refine le_min ?_ ?_
    · have h := integral_mono hmin_int (integrable_const (K : ℝ)) (fun ω => min_le_left _ _)
      simpa using h
    · calc ∫ ω, min (K : ℝ) (N ω) ≤ ∫ ω, N ω :=
            integral_mono hmin_int hN_int (fun ω => min_le_right _ _)
        _ = (K : ℝ) * ℓ := by rw [← hS_eq]
