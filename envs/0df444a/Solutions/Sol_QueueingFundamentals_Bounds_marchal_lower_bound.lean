-- Prove2me | solution 1 for QueueingFundamentals.Bounds.marchal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:49:51.687976+00:00
-- url     : https://prove2.me/submissions/2b9c64ed-316b-47a8-90dc-147d16283454

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1



namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

lemma qb_lindley_cont : Continuous (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) := by
  unfold lindley; fun_prop

lemma qb_idleX_cont : Continuous (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) := by
  unfold idleX; fun_prop

lemma qb_int_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ρ : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] (f : α → ℝ) :
    ∫ p, f p.1 ∂(μ.prod ρ) = ∫ w, f w ∂μ := by
  rw [integral_fun_fst]; simp

lemma qb_int_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ρ : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] (f : β → ℝ) :
    ∫ p, f p.2 ∂(μ.prod ρ) = ∫ w, f w ∂ρ := by
  rw [integral_fun_snd]; simp

section
variable {A B ν : Measure ℝ}

lemma qb_ae_nonneg
    (hinv : (stepLaw ν B A).map (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) = ν) :
    ∀ᵐ w ∂ν, 0 ≤ w := by
  rw [← hinv, ae_map_iff qb_lindley_cont.measurable.aemeasurable
    (measurableSet_Ici (a := (0:ℝ)))]
  exact Filter.Eventually.of_forall (fun p => le_max_left _ _)

lemma qb_integral_inv
    (hinv : (stepLaw ν B A).map (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) = ν)
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ p, g (lindley p.1 p.2.1 p.2.2) ∂(stepLaw ν B A) = ∫ w, g w ∂ν := by
  conv_rhs => rw [← hinv]
  rw [integral_map qb_lindley_cont.measurable.aemeasurable hg.aestronglyMeasurable]

lemma qb_integrable_inv
    (hinv : (stepLaw ν B A).map (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) = ν)
    {g : ℝ → ℝ} (hg : Measurable g) (hi : Integrable g ν) :
    Integrable (fun p => g (lindley p.1 p.2.1 p.2.2)) (stepLaw ν B A) := by
  rw [← hinv] at hi
  exact (integrable_map_measure hg.aestronglyMeasurable
    qb_lindley_cont.measurable.aemeasurable).1 hi

lemma qb_ae_of_nonneg_meas {μ : Measure ℝ} (h : μ (Set.Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  rw [ae_iff]; simpa [not_le, Set.Iio] using h

end

lemma qb_scalar1 (w u K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K) :
    (min (max (max 0 (w + u)) 0) K) ^ 2 - (min (max w 0) K) ^ 2 ≤
      2 * (if w ≤ K then w else 0) * u + (if w ≤ K then (1:ℝ) else 0) * u ^ 2 := by
  have hm : max (max 0 (w + u)) 0 = max 0 (w + u) := by simp
  rw [hm, max_eq_left hw]
  have h0 : 0 ≤ max 0 (w + u) := le_max_left _ _
  split_ifs with h
  · rw [min_eq_left h]
    have h1 : min (max 0 (w + u)) K ≤ max 0 (w + u) := min_le_left _ _
    have h2 : 0 ≤ min (max 0 (w + u)) K := le_min h0 hK
    have h3 : (max 0 (w + u)) ^ 2 ≤ (w + u) ^ 2 := by
      rcases le_total 0 (w + u) with h4 | h4
      · rw [max_eq_right h4]
      · rw [max_eq_left h4]; nlinarith [sq_nonneg (w + u)]
    nlinarith
  · push Not at h
    rw [min_eq_right h.le]
    have h1 : min (max 0 (w + u)) K ≤ K := min_le_right _ _
    have h2 : 0 ≤ min (max 0 (w + u)) K := le_min h0 hK
    nlinarith

section
variable {A B ν : Measure ℝ} [IsProbabilityMeasure A] [IsProbabilityMeasure B]
  [IsProbabilityMeasure ν]

lemma qb_integrable_W
    (hinv : (stepLaw ν B A).map (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) = ν)
    (hSm : MemLp (fun x : ℝ => x) 2 B) (hTm : MemLp (fun x : ℝ => x) 2 A)
    (hEU : ∫ q, (q.1 - q.2) ∂(B.prod A) < 0) : Integrable (fun w : ℝ => w) ν := by
  have hν0 := qb_ae_nonneg hinv
  have hP0 : ∀ᵐ p ∂(stepLaw ν B A), 0 ≤ p.1 := Measure.quasiMeasurePreserving_fst.ae hν0
  have hUm : MemLp (fun q : ℝ × ℝ => q.1 - q.2) 2 (B.prod A) :=
    (hSm.comp_fst A).sub (hTm.comp_snd B)
  have hU1 : Integrable (fun q : ℝ × ℝ => q.1 - q.2) (B.prod A) := hUm.integrable one_le_two
  have hU2 : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (B.prod A) := hUm.integrable_sq
  set EU := ∫ q, (q.1 - q.2) ∂(B.prod A) with hEUdef
  set EU2 := ∫ q, (q.1 - q.2) ^ 2 ∂(B.prod A) with hEU2def
  have hEU2 : 0 ≤ EU2 := integral_nonneg (fun q => sq_nonneg _)
  let a : ℕ → ℝ → ℝ := fun n w => if w ≤ (n:ℝ) then w else 0
  let b : ℕ → ℝ → ℝ := fun n w => if w ≤ (n:ℝ) then (1:ℝ) else 0
  have ha_meas : ∀ n, Measurable (a n) := fun n =>
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id measurable_const
  have hb_meas : ∀ n, Measurable (b n) := fun n =>
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
      measurable_const
  have ha_nn : ∀ n, ∀ᵐ w ∂ν, 0 ≤ a n w := fun n => by
    filter_upwards [hν0] with w hw
    simp only [a]; split_ifs <;> linarith
  have ha_int : ∀ n, Integrable (a n) ν := fun n => by
    refine Integrable.of_bound (ha_meas n).aestronglyMeasurable (n : ℝ) ?_
    filter_upwards [hν0] with w hw
    simp only [a]; split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_nonneg hw]; exact h
    · simp
  have hb_int : ∀ n, Integrable (b n) ν := fun n => by
    refine Integrable.of_bound (hb_meas n).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun w => by simp only [b]; split_ifs <;> simp)
  have hbound : ∀ n : ℕ, ∫ w, a n w ∂ν ≤ EU2 / (2 * (-EU)) := by
    intro n
    let g : ℝ → ℝ := fun x => (min (max x 0) (n:ℝ)) ^ 2
    have hg_meas : Measurable g := by
      simp only [g]; fun_prop
    have hg_int : Integrable g ν := by
      refine Integrable.of_bound hg_meas.aestronglyMeasurable ((n:ℝ) ^ 2) ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [g, Real.norm_eq_abs]
      have h1 : 0 ≤ min (max x 0) (n:ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg n)
      have h2 : min (max x 0) (n:ℝ) ≤ n := min_le_right _ _
      rw [abs_of_nonneg (by positivity)]; nlinarith
    have hinvg := qb_integral_inv hinv hg_meas
    have hfst : ∫ p, g p.1 ∂(stepLaw ν B A) = ∫ w, g w ∂ν := qb_int_fst _ _ g
    have hI1 : Integrable (fun p : ℝ × ℝ × ℝ => g (lindley p.1 p.2.1 p.2.2)) (stepLaw ν B A) :=
      qb_integrable_inv hinv hg_meas hg_int
    have hI2 : Integrable (fun p : ℝ × ℝ × ℝ => g p.1) (stepLaw ν B A) := hg_int.comp_fst _
    have hR1 : Integrable (fun p : ℝ × ℝ × ℝ => (2 * a n p.1) * (p.2.1 - p.2.2))
        (stepLaw ν B A) := ((ha_int n).const_mul 2).mul_prod hU1
    have hR2 : Integrable (fun p : ℝ × ℝ × ℝ => b n p.1 * (p.2.1 - p.2.2) ^ 2)
        (stepLaw ν B A) := (hb_int n).mul_prod hU2
    have hmono : ∫ p, (g (lindley p.1 p.2.1 p.2.2) - g p.1) ∂(stepLaw ν B A) ≤
        ∫ p, ((2 * a n p.1) * (p.2.1 - p.2.2) + b n p.1 * (p.2.1 - p.2.2) ^ 2)
          ∂(stepLaw ν B A) := by
      refine integral_mono_ae (hI1.sub hI2) (hR1.add hR2) ?_
      filter_upwards [hP0] with p hp
      have := qb_scalar1 p.1 (p.2.1 - p.2.2) n hp (Nat.cast_nonneg n)
      simp only [g, a, b, lindley]
      linarith
    rw [integral_sub hI1 hI2, hinvg, hfst, sub_self, integral_add hR1 hR2] at hmono
    have e1 : ∫ p, (2 * a n p.1) * (p.2.1 - p.2.2) ∂(stepLaw ν B A) =
        (∫ w, 2 * a n w ∂ν) * EU := by
      unfold stepLaw; exact integral_prod_mul (fun w => 2 * a n w) (fun q : ℝ × ℝ => q.1 - q.2)
    have e2 : ∫ p, b n p.1 * (p.2.1 - p.2.2) ^ 2 ∂(stepLaw ν B A) =
        (∫ w, b n w ∂ν) * EU2 := by
      unfold stepLaw; exact integral_prod_mul (fun w => b n w) (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2)
    rw [e1, e2, integral_const_mul] at hmono
    have hb1 : ∫ w, b n w ∂ν ≤ 1 := by
      calc ∫ w, b n w ∂ν ≤ ∫ w, (1:ℝ) ∂ν :=
            integral_mono (hb_int n) (integrable_const _)
              (fun w => by simp only [b]; split_ifs <;> norm_num)
        _ = 1 := by simp
    have hb0 : 0 ≤ ∫ w, b n w ∂ν :=
      integral_nonneg (fun w => by simp only [b]; split_ifs <;> norm_num)
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  refine integrable_of_tendsto (G := a) ?_ (fun n => (ha_meas n).aestronglyMeasurable) ?_
  · refine Filter.Eventually.of_forall (fun w => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈w⌉₊] with n hn
    have : w ≤ (n:ℝ) := (Nat.le_ceil w).trans (by exact_mod_cast hn)
    simp only [a, if_pos this]
  · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := EU2 / (2 * (-EU)))) ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall (fun n => ?_))
    have : ∫⁻ x, ‖a n x‖ₑ ∂ν = ∫⁻ x, ENNReal.ofReal (a n x) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [ha_nn n] with x hx using Real.enorm_of_nonneg hx
    rw [this, ← ofReal_integral_eq_lintegral_ofReal (ha_int n) (ha_nn n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)

end

lemma qb_idle_eq (w s t : ℝ) : idleX w s t = lindley w s t - (w + (s - t)) := by
  unfold idleX lindley
  rcases le_total 0 (w + (s - t)) with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

lemma qb_phi_lip (a b : ℝ) :
    |(max a 0) ^ 2 - (max b 0) ^ 2| ≤ |a - b| * (max a 0 + max b 0) := by
  have h1 : (max a 0) ^ 2 - (max b 0) ^ 2 = (max a 0 - max b 0) * (max a 0 + max b 0) := by ring
  rw [h1, abs_mul, abs_of_nonneg (add_nonneg (le_max_right a 0) (le_max_right b 0))]
  exact mul_le_mul_of_nonneg_right (abs_max_sub_max_le_abs a b 0)
    (add_nonneg (le_max_right a 0) (le_max_right b 0))

lemma qb_key_identity (w u K : ℝ) (hK : 0 ≤ K) :
    ((max 0 (w + u)) ^ 2 - (max (max 0 (w + u) - K) 0) ^ 2) + (-min 0 (w + u)) ^ 2
      - (w ^ 2 - (max (w - K) 0) ^ 2) =
      2 * w * u + u ^ 2 - ((max (w + u - K) 0) ^ 2 - (max (w - K) 0) ^ 2) := by
  rcases le_total 0 (w + u) with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]
    have h1 : max (0 - K) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (w + u - K) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]; ring

section
variable {A B ν : Measure ℝ} [IsProbabilityMeasure A] [IsProbabilityMeasure B]
  [IsProbabilityMeasure ν]

lemma qb_main
    (hinv : (stepLaw ν B A).map (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) = ν)
    (hSm : MemLp (fun x : ℝ => x) 2 B) (hTm : MemLp (fun x : ℝ => x) 2 A)
    (hB0 : B (Set.Iio 0) = 0) (hA0 : A (Set.Iio 0) = 0)
    (hEU : ∫ q, (q.1 - q.2) ∂(B.prod A) < 0) :
    Integrable (fun w : ℝ => w) ν ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = -∫ q, (q.1 - q.2) ∂(B.prod A) ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) =
      ∫ q, (q.1 - q.2) ^ 2 ∂(B.prod A) + 2 * (∫ q, (q.1 - q.2) ∂(B.prod A)) * ∫ w, w ∂ν ∧
    MemLp (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) 2 (stepLaw ν B A) ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) ≤ ∫ t, t ^ 2 ∂A := by
  have hW := qb_integrable_W hinv hSm hTm hEU
  have hν0 := qb_ae_nonneg hinv
  have hP0 : ∀ᵐ p ∂(stepLaw ν B A), 0 ≤ p.1 := Measure.quasiMeasurePreserving_fst.ae hν0
  have hPs : ∀ᵐ p ∂(stepLaw ν B A), 0 ≤ p.2.1 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_fst.ae (qb_ae_of_nonneg_meas hB0))
  have hPt : ∀ᵐ p ∂(stepLaw ν B A), 0 ≤ p.2.2 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_snd.ae (qb_ae_of_nonneg_meas hA0))
  have hUm : MemLp (fun q : ℝ × ℝ => q.1 - q.2) 2 (B.prod A) :=
    (hSm.comp_fst A).sub (hTm.comp_snd B)
  have hU1 : Integrable (fun q : ℝ × ℝ => q.1 - q.2) (B.prod A) := hUm.integrable one_le_two
  have hU2 : Integrable (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (B.prod A) := hUm.integrable_sq
  have hT2 : Integrable (fun t : ℝ => t ^ 2) A := hTm.integrable_sq
  have hWP : Integrable (fun p : ℝ × ℝ × ℝ => p.1) (stepLaw ν B A) := hW.comp_fst _
  have hUP : Integrable (fun p : ℝ × ℝ × ℝ => p.2.1 - p.2.2) (stepLaw ν B A) :=
    hU1.comp_snd ν
  have hU2P : Integrable (fun p : ℝ × ℝ × ℝ => (p.2.1 - p.2.2) ^ 2) (stepLaw ν B A) :=
    hU2.comp_snd ν
  have hLP : Integrable (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) (stepLaw ν B A) :=
    qb_integrable_inv hinv (g := fun w => w) measurable_id hW
  have hXeq : (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) =
      fun p => lindley p.1 p.2.1 p.2.2 - (p.1 + (p.2.1 - p.2.2)) := by
    funext p; exact qb_idle_eq _ _ _
  have hXP : Integrable (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) (stepLaw ν B A) := by
    rw [hXeq]; exact hLP.sub (hWP.add hUP)
  have eW : ∫ p, p.1 ∂(stepLaw ν B A) = ∫ w, w ∂ν := qb_int_fst _ _ (fun w => w)
  have eU : ∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) = ∫ q, (q.1 - q.2) ∂(B.prod A) :=
    qb_int_snd _ _ (fun q : ℝ × ℝ => q.1 - q.2)
  have eU2 : ∫ p, (p.2.1 - p.2.2) ^ 2 ∂(stepLaw ν B A) = ∫ q, (q.1 - q.2) ^ 2 ∂(B.prod A) :=
    qb_int_snd _ _ (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2)
  have eL : ∫ p, lindley p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = ∫ w, w ∂ν :=
    qb_integral_inv hinv (g := fun w => w) measurable_id
  have eX : ∫ p, idleX p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = -∫ q, (q.1 - q.2) ∂(B.prod A) := by
    have hWU' : Integrable (fun p : ℝ × ℝ × ℝ => p.1 + (p.2.1 - p.2.2)) (stepLaw ν B A) :=
      hWP.add hUP
    rw [hXeq, integral_sub hLP hWU', integral_add hWP hUP, eL, eW, eU]; ring
  -- bounds on X
  have hX_nn : ∀ p : ℝ × ℝ × ℝ, 0 ≤ idleX p.1 p.2.1 p.2.2 := fun p => by
    unfold idleX; simp
  have hX_le : ∀ᵐ p ∂(stepLaw ν B A), idleX p.1 p.2.1 p.2.2 ≤ p.2.2 := by
    filter_upwards [hP0, hPs, hPt] with p h1 h2 h3
    unfold idleX
    rcases le_total 0 (p.1 + (p.2.1 - p.2.2)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hXsm : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2)
      (stepLaw ν B A) := qb_idleX_cont.measurable.aestronglyMeasurable
  have hT2P : Integrable (fun p : ℝ × ℝ × ℝ => p.2.2 ^ 2) (stepLaw ν B A) :=
    (hT2.comp_snd B).comp_snd ν
  have hX2 : Integrable (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2 ^ 2) (stepLaw ν B A) := by
    refine hT2P.mono' (hXsm.pow 2) ?_
    filter_upwards [hX_le] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hX_nn p
    nlinarith
  have hXm : MemLp (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) 2 (stepLaw ν B A) :=
    (memLp_two_iff_integrable_sq hXsm).2 hX2
  have hXT : ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) ≤ ∫ t, t ^ 2 ∂A := by
    have : ∫ p, p.2.2 ^ 2 ∂(stepLaw ν B A) = ∫ t, t ^ 2 ∂A := by
      unfold stepLaw
      rw [qb_int_snd ν (B.prod A) (fun q : ℝ × ℝ => q.2 ^ 2), qb_int_snd B A (fun t => t ^ 2)]
    rw [← this]
    refine integral_mono_ae hX2 hT2P ?_
    filter_upwards [hX_le] with p hp
    have := hX_nn p
    nlinarith
  refine ⟨hW, eX, ?_, hXm, hXT⟩
  -- exact second-moment identity
  set c := ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) -
    (∫ q, (q.1 - q.2) ^ 2 ∂(B.prod A) + 2 * (∫ q, (q.1 - q.2) ∂(B.prod A)) * ∫ w, w ∂ν)
    with hc
  suffices hc0 : c = 0 by linarith
  let D : ℕ → ℝ × ℝ × ℝ → ℝ := fun n p =>
    (max (p.1 - n) 0) ^ 2 - (max (p.1 + (p.2.1 - p.2.2) - n) 0) ^ 2
  have hWU : Integrable (fun p : ℝ × ℝ × ℝ => p.1 * (p.2.1 - p.2.2)) (stepLaw ν B A) :=
    hW.mul_prod hU1
  have eWU : ∫ p, p.1 * (p.2.1 - p.2.2) ∂(stepLaw ν B A) =
      (∫ w, w ∂ν) * ∫ q, (q.1 - q.2) ∂(B.prod A) := by
    unfold stepLaw; exact integral_prod_mul (fun w => w) (fun q : ℝ × ℝ => q.1 - q.2)
  have hDint : ∀ n : ℕ, ∫ p, D n p ∂(stepLaw ν B A) = c := by
    intro n
    let h : ℝ → ℝ := fun x => x ^ 2 - (max (x - n) 0) ^ 2
    have hh_meas : Measurable h := by simp only [h]; fun_prop
    have hh_int : Integrable h ν := by
      have hb : Integrable (fun x : ℝ => 2 * n * |x| + (n:ℝ) ^ 2) ν :=
        ((hW.abs).const_mul (2 * n)).add (integrable_const ((n:ℝ) ^ 2))
      refine hb.mono' hh_meas.aestronglyMeasurable ?_
      filter_upwards [hν0] with x hx
      simp only [h, Real.norm_eq_abs]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [abs_of_nonneg hx]
      rcases le_total x n with hxn | hxn
      · rw [max_eq_right (by linarith)]
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [max_eq_left (by linarith)]
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have hhL := qb_integrable_inv hinv hh_meas hh_int
    have ehL := qb_integral_inv hinv hh_meas
    have hhW : Integrable (fun p : ℝ × ℝ × ℝ => h p.1) (stepLaw ν B A) := hh_int.comp_fst _
    have ehW : ∫ p, h p.1 ∂(stepLaw ν B A) = ∫ w, h w ∂ν := qb_int_fst _ _ h
    have hDe : ∀ p : ℝ × ℝ × ℝ, D n p =
        (h (lindley p.1 p.2.1 p.2.2) - h p.1) +
          (idleX p.1 p.2.1 p.2.2 ^ 2 - (2 * (p.1 * (p.2.1 - p.2.2)) + (p.2.1 - p.2.2) ^ 2)) := by
      intro p
      have := qb_key_identity p.1 (p.2.1 - p.2.2) n (Nat.cast_nonneg n)
      simp only [D, h, lindley, idleX]
      linarith
    rw [show (fun p => D n p) = fun p => (h (lindley p.1 p.2.1 p.2.2) - h p.1) +
          (idleX p.1 p.2.1 p.2.2 ^ 2 - (2 * (p.1 * (p.2.1 - p.2.2)) + (p.2.1 - p.2.2) ^ 2))
        from funext hDe]
    have i1 : Integrable (fun p : ℝ × ℝ × ℝ => 2 * (p.1 * (p.2.1 - p.2.2))) (stepLaw ν B A) :=
      hWU.const_mul 2
    have i2 : Integrable (fun p : ℝ × ℝ × ℝ => 2 * (p.1 * (p.2.1 - p.2.2)) + (p.2.1 - p.2.2) ^ 2)
        (stepLaw ν B A) := i1.add hU2P
    have i3 : Integrable (fun p : ℝ × ℝ × ℝ => h (lindley p.1 p.2.1 p.2.2) - h p.1)
        (stepLaw ν B A) := hhL.sub hhW
    have i4 : Integrable (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2 ^ 2 -
        (2 * (p.1 * (p.2.1 - p.2.2)) + (p.2.1 - p.2.2) ^ 2)) (stepLaw ν B A) := hX2.sub i2
    rw [integral_add i3 i4,
      integral_sub hhL hhW, integral_sub hX2 i2,
      integral_add i1 hU2P, integral_const_mul, ehL, ehW, eWU, eU2, hc]
    ring
  have hlim : Tendsto (fun n : ℕ => ∫ p, D n p ∂(stepLaw ν B A)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence
      (μ := stepLaw ν B A) (F := D) (f := fun _ => (0:ℝ))
      (fun p => 2 * (|p.1| * |p.2.1 - p.2.2|) + (p.2.1 - p.2.2) ^ 2)
      (fun n => by
        refine Continuous.aestronglyMeasurable ?_
        simp only [D]; fun_prop)
      (by
        have j1 : Integrable (fun p : ℝ × ℝ × ℝ => |p.1| * |p.2.1 - p.2.2|) (stepLaw ν B A) :=
          hW.abs.mul_prod hU1.abs
        exact (j1.const_mul 2).add hU2P)
      (fun n => Filter.Eventually.of_forall (fun p => by
        simp only [D, Real.norm_eq_abs]
        have hl := qb_phi_lip (p.1 - n) (p.1 + (p.2.1 - p.2.2) - n)
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
        have e1 : |p.1 - n - (p.1 + (p.2.1 - p.2.2) - n)| = |p.2.1 - p.2.2| := by
          rw [show p.1 - n - (p.1 + (p.2.1 - p.2.2) - n) = -(p.2.1 - p.2.2) by ring, abs_neg]
        have m1 : max (p.1 - n) 0 ≤ |p.1| :=
          max_le (by linarith [le_abs_self p.1]) (abs_nonneg _)
        have m2 : max (p.1 + (p.2.1 - p.2.2) - n) 0 ≤ |p.1| + |p.2.1 - p.2.2| :=
          max_le (by linarith [le_abs_self p.1, le_abs_self (p.2.1 - p.2.2)])
            (add_nonneg (abs_nonneg _) (abs_nonneg _))
        rw [e1] at hl
        have hsq : |p.2.1 - p.2.2| ^ 2 = (p.2.1 - p.2.2) ^ 2 := sq_abs _
        nlinarith [abs_nonneg (p.2.1 - p.2.2), abs_nonneg p.1]))
      (Filter.Eventually.of_forall (fun p => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈max p.1 (p.1 + (p.2.1 - p.2.2))⌉₊] with n hn
        have h1 : max p.1 (p.1 + (p.2.1 - p.2.2)) ≤ (n:ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hn)
        have h2 : p.1 - n ≤ 0 := by linarith [le_max_left p.1 (p.1 + (p.2.1 - p.2.2))]
        have h3 : p.1 + (p.2.1 - p.2.2) - n ≤ 0 := by
          linarith [le_max_right p.1 (p.1 + (p.2.1 - p.2.2))]
        simp only [D, max_eq_right h2, max_eq_right h3]; ring))
    simpa using this
  have hconst : Tendsto (fun n : ℕ => ∫ p, D n p ∂(stepLaw ν B A)) atTop (𝓝 c) := by
    simp only [hDint]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst hlim

end

lemma qb_moments {A B : Measure ℝ} {lam mu : ℝ} (hin : IsGG1Input A B lam mu) :
    ∫ q, (q.1 - q.2) ∂(B.prod A) = 1 / mu - 1 / lam ∧
    ∫ q, (q.1 - q.2) ^ 2 ∂(B.prod A) =
      serviceVar B + interarrivalVar A + (1 / mu - 1 / lam) ^ 2 ∧
    ∫ t, t ^ 2 ∂A = interarrivalVar A + (1 / lam) ^ 2 := by
  haveI := hin.isProbability_interarrival
  haveI := hin.isProbability_service
  have hSm := hin.service_memLp
  have hTm := hin.interarrival_memLp
  have hS1 : Integrable (fun x : ℝ => x) B := hSm.integrable one_le_two
  have hT1 : Integrable (fun x : ℝ => x) A := hTm.integrable one_le_two
  have eU : ∫ q, (q.1 - q.2) ∂(B.prod A) = 1 / mu - 1 / lam := by
    rw [integral_sub (hS1.comp_fst A) (hT1.comp_snd B), qb_int_fst B A (fun x => x),
      qb_int_snd B A (fun x => x), hin.service_mean, hin.interarrival_mean]
  have hUm : MemLp (fun q : ℝ × ℝ => q.1 - q.2) 2 (B.prod A) :=
    (hSm.comp_fst A).sub (hTm.comp_snd B)
  have hvarU : variance (fun q : ℝ × ℝ => q.1 - q.2) (B.prod A) =
      serviceVar B + interarrivalVar A := by
    have h := variance_add_prod (X := fun x : ℝ => x) (Y := fun x : ℝ => -x) hSm hTm.neg
    rw [variance_fun_neg] at h
    simp only [← sub_eq_add_neg] at h
    rw [h]; rfl
  have hvU := variance_eq_sub hUm
  have hvT := variance_eq_sub hTm
  simp only [Pi.pow_apply] at hvU hvT
  refine ⟨eU, ?_, ?_⟩
  · rw [hvarU, eU] at hvU; linarith
  · unfold interarrivalVar; rw [hvT, hin.interarrival_mean]; ring

lemma qb_all {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) =
      serviceVar B + interarrivalVar A + (1 / mu - 1 / lam) ^ 2 +
        2 * (1 / mu - 1 / lam) * meanWait ν ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = 1 / lam - 1 / mu ∧
    MemLp (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) 2 (stepLaw ν B A) ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) ≤ interarrivalVar A + (1 / lam) ^ 2 ∧
    (1 / lam - 1 / mu) ^ 2 ≤ ∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) ∧
    0 < 1 / lam - 1 / mu ∧ 1 - lam / mu = lam * (1 / lam - 1 / mu) := by
  haveI := hin.isProbability_interarrival
  haveI := hin.isProbability_service
  haveI := hν.isProbability
  haveI : IsProbabilityMeasure (stepLaw ν B A) := by unfold stepLaw; infer_instance
  obtain ⟨eU, eU2, eT2⟩ := qb_moments hin
  have hlm : lam < mu := by rwa [div_lt_one hmu] at hrho
  have hm : 0 < 1 / lam - 1 / mu := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt hlam hlm
  have hEU : ∫ q, (q.1 - q.2) ∂(B.prod A) < 0 := by rw [eU]; linarith
  obtain ⟨hW, eX, eX2, hXm, hXT⟩ := qb_main hν.invariant hin.service_memLp
    hin.interarrival_memLp hin.service_nonneg hin.interarrival_nonneg hEU
  have hv := variance_eq_sub hXm
  have hv0 := variance_nonneg (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) (stepLaw ν B A)
  simp only [Pi.pow_apply] at hv
  rw [eU] at eX
  refine ⟨hW, ?_, ?_, hXm, ?_, ?_, hm, ?_⟩
  · rw [eX2, eU, eU2]; rfl
  · rw [eX]; ring
  · rw [← eT2]; exact hXT
  · have : ∫ p, idleX p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = 1 / lam - 1 / mu := by rw [eX]; ring
    rw [← this]; linarith
  · field_simp

theorem kingman_core {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    meanWait ν ≤ lam * (interarrivalVar A + serviceVar B) / (2 * (1 - lam / mu)) := by
  obtain ⟨hW, e2, -, -, -, hge, hm, hr⟩ := qb_all hlam hmu hin hrho hν
  refine ⟨hW, ?_⟩
  rw [hr, le_div_iff₀ (by positivity)]
  have key : 2 * (1 / lam - 1 / mu) * meanWait ν ≤ interarrivalVar A + serviceVar B := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hlam.le]

theorem marchal_core {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    (lam ^ 2 * serviceVar B + lam / mu * (lam / mu - 2)) / (2 * lam * (1 - lam / mu)) ≤
      meanWait ν := by
  obtain ⟨hW, e2, -, -, hle, -, hm, hr⟩ := qb_all hlam hmu hin hrho hν
  refine ⟨hW, ?_⟩
  have hrho' : lam / mu = 1 - lam * (1 / lam - 1 / mu) := by linarith
  set m := 1 / lam - 1 / mu with hmdef
  rw [hr, div_le_iff₀ (by positivity), hrho']
  have key : serviceVar B + m ^ 2 - (1 / lam) ^ 2 ≤ 2 * m * meanWait ν := by
    have : (1 / mu - 1 / lam) = -m := by rw [hmdef]; ring
    rw [this] at e2; nlinarith
  have h2 := mul_le_mul_of_nonneg_left key (sq_nonneg lam)
  have h3 : lam ^ 2 * (1 / lam) ^ 2 = 1 := by field_simp
  nlinarith

theorem mean_wait_core {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    meanWait ν =
      (∫ p, idleX p.1 p.2.1 p.2.2 ^ 2 ∂(stepLaw ν B A) - ∫ p, (p.2.1 - p.2.2) ^ 2 ∂(stepLaw ν B A)) /
        (2 * ∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A)) := by
  haveI := hin.isProbability_interarrival
  haveI := hin.isProbability_service
  haveI := hν.isProbability
  obtain ⟨hW, e2, -, -, -, -, hm, -⟩ := qb_all hlam hmu hin hrho hν
  obtain ⟨eU, eU2, -⟩ := qb_moments hin
  refine ⟨hW, ?_⟩
  have a1 : ∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) = 1 / mu - 1 / lam := by
    unfold stepLaw; rw [qb_int_snd ν (B.prod A) (fun q : ℝ × ℝ => q.1 - q.2), eU]
  have a2 : ∫ p, (p.2.1 - p.2.2) ^ 2 ∂(stepLaw ν B A) =
      serviceVar B + interarrivalVar A + (1 / mu - 1 / lam) ^ 2 := by
    unfold stepLaw; rw [qb_int_snd ν (B.prod A) (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2), eU2]
  rw [a1, a2, e2, eq_div_iff (by intro h; linarith)]
  ring

theorem departure_core {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    variance (fun q : ℝ × (ℝ × ℝ × ℝ) => q.1 + idleX q.2.1 q.2.2.1 q.2.2.2)
        (B.prod (stepLaw ν B A)) =
      2 * serviceVar B + interarrivalVar A - 2 * meanWait ν * (1 / lam - 1 / mu) := by
  haveI := hin.isProbability_interarrival
  haveI := hin.isProbability_service
  haveI := hν.isProbability
  haveI : IsProbabilityMeasure (stepLaw ν B A) := by unfold stepLaw; infer_instance
  obtain ⟨hW, e2, e1, hXm, -, -, hm, -⟩ := qb_all hlam hmu hin hrho hν
  refine ⟨hW, ?_⟩
  have h := variance_add_prod (X := fun x : ℝ => x)
    (Y := fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) hin.service_memLp hXm
  rw [h, variance_eq_sub hXm]
  simp only [Pi.pow_apply]
  rw [e1, e2]
  unfold serviceVar
  ring

end QueueingFundamentals.Bounds

open QueueingFundamentals.Bounds
open MeasureTheory ProbabilityTheory Filter Topology

theorem solution
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    (lam ^ 2 * serviceVar B + lam / mu * (lam / mu - 2)) / (2 * lam * (1 - lam / mu)) ≤
      meanWait ν := by
  exact marchal_core hlam hmu hin hrho hν
