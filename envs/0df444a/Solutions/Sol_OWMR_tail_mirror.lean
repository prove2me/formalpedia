-- Prove2me | solution 1 for OWMR.tail_mirror
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:07.186215+00:00
-- url     : https://prove2.me/submissions/0f5a0e5e-fa96-4740-a778-a213dad5b9a8

import Theorems.Thm_OWMR_renewal_doubling
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Lemma 6 (tail-mirror inequality), for any `B` with `B M(b) ≤ V_z` at every center `z`.

Step 1 (doubling): by Tonelli's theorem, `𝒯_b = ∫_0^b U[b, b+s) ds` and
`2 ∫_{[0,b)} (x - b/2)⁺ U(dx) = ∫_0^b U[(b+s)/2, b) ds`; with `u = (b+s)/2`, the doubling bound
`U[u, 2u) ≤ M(u)` gives `U[b, 2u) + 2 U[u, b) ≤ M(b)` for every `s`, so
`𝒯_b + 4 ∫_{[0,b)} (x - b/2)⁺ U(dx) ≤ b M(b)`.
Steps 2 and 3: the two fixed mirror centers `z = 0` and `z = b/2` and the identity
`x = (x - b/2)⁺ - (b/2 - x)⁺ + b/2` turn this bound into (17).
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

private lemma swap_count (U : Measure ℝ) [SFinite U] (A B : Set ℝ) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) :
    ∫⁻ y in A, ((volume : Measure ℝ).restrict B) (Prod.mk y ⁻¹' S) ∂U
      = ∫⁻ t in B, (U.restrict A) ((fun y => (y, t)) ⁻¹' S) := by
  rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]

private lemma intOn (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {a e : ℝ} (ha : 0 ≤ a) :
    IntegrableOn φ (Set.Ico a e) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C)
    (ne_top_of_le_ne_top (renewalMeasure_Ico_lt_top ρ hρ e).ne
      (measure_mono (Set.Ico_subset_Ico_left ha))) hφ.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hC x (Set.Ico_subset_Icc_self hx)

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (h p b : ℝ) (hh : 0 < h) (hp : 0 < p) (hb : 0 < b)
    (B : ℝ) (hB : ∀ z : ℝ, B * (renewalMeasure ρ (Set.Ico 0 b)).toReal
      ≤ ∫ x in Set.Ico 0 b, (p * max (z - x) 0 + h * max (x - z) 0) ∂(renewalMeasure ρ)) :
    p * ∫ x in Set.Ico b (2 * b), (2 * b - x) ∂(renewalMeasure ρ)
        + 4 * (p / h) * (renewalMeasure ρ (Set.Ico 0 b)).toReal * B
      ≤ (3 * (p / h) + 1) * (h * p / (h + p)) * b * (renewalMeasure ρ (Set.Ico 0 b)).toReal := by
  have : SFinite (renewalMeasure ρ) := by unfold renewalMeasure; infer_instance
  have hUb : renewalMeasure ρ (Set.Ico 0 b) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hρ b).ne
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (renewalMeasure ρ (Set.Ico 0 b)).toReal := ⟨_, rfl⟩
  rw [← hM] at hB ⊢
  have hM0 : 0 ≤ M := hM ▸ ENNReal.toReal_nonneg
  -- Step 1: the doubling bound, integrated by Tonelli's theorem
  have hS1 : MeasurableSet {q : ℝ × ℝ | q.1 < b + q.2} :=
    measurableSet_lt measurable_fst (measurable_const.add measurable_snd)
  have hS2 : MeasurableSet {q : ℝ × ℝ | b + q.2 ≤ 2 * q.1} :=
    measurableSet_le (measurable_const.add measurable_snd) (measurable_const.mul measurable_fst)
  have hE1 : ∫⁻ x in Set.Ico b (2 * b), ENNReal.ofReal (2 * b - x) ∂(renewalMeasure ρ)
      = ∫⁻ s in Set.Ico 0 b, renewalMeasure ρ (Set.Ico b (b + s)) := by
    calc ∫⁻ x in Set.Ico b (2 * b), ENNReal.ofReal (2 * b - x) ∂(renewalMeasure ρ)
        = ∫⁻ x in Set.Ico b (2 * b), ((volume : Measure ℝ).restrict (Set.Ico 0 b))
            (Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 < b + q.2}) ∂(renewalMeasure ρ) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun x hx => ?_
          have e : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 < b + q.2} = Set.Ioi (x - b) := by
            ext s
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioi]
            constructor <;> intro h' <;> linarith
          have e2 : Set.Ioi (x - b) ∩ Set.Ico 0 b = Set.Ioo (x - b) b := by
            ext s
            simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ico, Set.mem_Ioo]
            constructor
            · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hx.1], h2⟩
          rw [e, Measure.restrict_apply measurableSet_Ioi, e2, Real.volume_Ioo]
          congr 1
          ring
      _ = ∫⁻ s in Set.Ico 0 b, ((renewalMeasure ρ).restrict (Set.Ico b (2 * b)))
            ((fun x => (x, s)) ⁻¹' {q : ℝ × ℝ | q.1 < b + q.2}) := swap_count _ _ _ hS1
      _ = ∫⁻ s in Set.Ico 0 b, renewalMeasure ρ (Set.Ico b (b + s)) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun s hs => ?_
          have e : (fun x => (x, s)) ⁻¹' {q : ℝ × ℝ | q.1 < b + q.2} = Set.Iio (b + s) := by
            ext x; simp
          have e2 : Set.Iio (b + s) ∩ Set.Ico b (2 * b) = Set.Ico b (b + s) := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
            constructor
            · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hs.2]⟩
          rw [e, Measure.restrict_apply measurableSet_Iio, e2]
  have hE2 : ∫⁻ x in Set.Ico 0 b, ENNReal.ofReal (2 * x - b) ∂(renewalMeasure ρ)
      = ∫⁻ s in Set.Ico 0 b, renewalMeasure ρ (Set.Ico ((b + s) / 2) b) := by
    calc ∫⁻ x in Set.Ico 0 b, ENNReal.ofReal (2 * x - b) ∂(renewalMeasure ρ)
        = ∫⁻ x in Set.Ico 0 b, ((volume : Measure ℝ).restrict (Set.Ico 0 b))
            (Prod.mk x ⁻¹' {q : ℝ × ℝ | b + q.2 ≤ 2 * q.1}) ∂(renewalMeasure ρ) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun x hx => ?_
          have e : Prod.mk x ⁻¹' {q : ℝ × ℝ | b + q.2 ≤ 2 * q.1} = Set.Iic (2 * x - b) := by
            ext s
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iic]
            constructor <;> intro h' <;> linarith
          have e2 : Set.Iic (2 * x - b) ∩ Set.Ico 0 b = Set.Icc 0 (2 * x - b) := by
            ext s
            simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
            constructor
            · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hx.2]⟩
          rw [e, Measure.restrict_apply measurableSet_Iic, e2, Real.volume_Icc, sub_zero]
      _ = ∫⁻ s in Set.Ico 0 b, ((renewalMeasure ρ).restrict (Set.Ico 0 b))
            ((fun x => (x, s)) ⁻¹' {q : ℝ × ℝ | b + q.2 ≤ 2 * q.1}) := swap_count _ _ _ hS2
      _ = ∫⁻ s in Set.Ico 0 b, renewalMeasure ρ (Set.Ico ((b + s) / 2) b) := by
          refine setLIntegral_congr_fun measurableSet_Ico fun s hs => ?_
          have e : (fun x => (x, s)) ⁻¹' {q : ℝ × ℝ | b + q.2 ≤ 2 * q.1}
              = Set.Ici ((b + s) / 2) := by
            ext x
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ici]
            constructor <;> intro h' <;> linarith
          have e2 : Set.Ici ((b + s) / 2) ∩ Set.Ico 0 b = Set.Ico ((b + s) / 2) b := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico]
            constructor
            · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hs.1], h2⟩
          rw [e, Measure.restrict_apply measurableSet_Ici, e2]
  -- the pointwise consequence of the doubling bound
  have hpt : ∀ s ∈ Set.Ico (0 : ℝ) b, renewalMeasure ρ (Set.Ico b (b + s))
      + 2 * renewalMeasure ρ (Set.Ico ((b + s) / 2) b) ≤ renewalMeasure ρ (Set.Ico 0 b) := by
    intro s hs
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (b + s) / 2 := ⟨_, rfl⟩
    rw [← hu, show b + s = 2 * u by rw [hu]; ring]
    have hu0 : 0 ≤ u := by rw [hu]; linarith [hs.1]
    have hub : u ≤ b := by rw [hu]; linarith [hs.2]
    have hb2u : b ≤ 2 * u := by rw [hu]; linarith [hs.1]
    have hfin : renewalMeasure ρ (Set.Ico 0 u) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hρ u).ne
    have hsplit1 : renewalMeasure ρ (Set.Ico 0 b)
        = renewalMeasure ρ (Set.Ico 0 u) + renewalMeasure ρ (Set.Ico u b) := by
      rw [← measure_union Set.Ico_disjoint_Ico_same measurableSet_Ico,
        Set.Ico_union_Ico_eq_Ico hu0 hub]
    have hsplit2 : renewalMeasure ρ (Set.Ico 0 (2 * u))
        = renewalMeasure ρ (Set.Ico 0 b) + renewalMeasure ρ (Set.Ico b (2 * u)) := by
      rw [← measure_union Set.Ico_disjoint_Ico_same measurableSet_Ico,
        Set.Ico_union_Ico_eq_Ico hb.le hb2u]
    have hD := renewal_doubling ρ u hu0
    rw [hsplit2, hsplit1, two_mul (renewalMeasure ρ (Set.Ico 0 u)), add_assoc] at hD
    have hcd := (ENNReal.add_le_add_iff_left hfin).1 hD
    rw [hsplit1, two_mul (renewalMeasure ρ (Set.Ico u b))]
    calc renewalMeasure ρ (Set.Ico b (2 * u))
          + (renewalMeasure ρ (Set.Ico u b) + renewalMeasure ρ (Set.Ico u b))
        = (renewalMeasure ρ (Set.Ico u b) + renewalMeasure ρ (Set.Ico b (2 * u)))
          + renewalMeasure ρ (Set.Ico u b) := by ring
      _ ≤ renewalMeasure ρ (Set.Ico 0 u) + renewalMeasure ρ (Set.Ico u b) :=
          add_le_add hcd le_rfl
  have hf_mono : Monotone fun s : ℝ => renewalMeasure ρ (Set.Ico b (b + s)) := fun s s' hss' =>
    measure_mono (Set.Ico_subset_Ico_right (by linarith))
  have hg_anti : Antitone fun s : ℝ => renewalMeasure ρ (Set.Ico ((b + s) / 2) b) :=
    fun s s' hss' => measure_mono (Set.Ico_subset_Ico_left (by linarith))
  have hEsum : ∫⁻ x in Set.Ico b (2 * b), ENNReal.ofReal (2 * b - x) ∂(renewalMeasure ρ)
      + 2 * ∫⁻ x in Set.Ico 0 b, ENNReal.ofReal (2 * x - b) ∂(renewalMeasure ρ)
      ≤ renewalMeasure ρ (Set.Ico 0 b) * ENNReal.ofReal b := by
    rw [hE1, hE2, ← lintegral_const_mul _ hg_anti.measurable,
      ← lintegral_add_left hf_mono.measurable]
    calc ∫⁻ s in Set.Ico 0 b, (renewalMeasure ρ (Set.Ico b (b + s))
            + 2 * renewalMeasure ρ (Set.Ico ((b + s) / 2) b))
        ≤ ∫⁻ _s in Set.Ico 0 b, renewalMeasure ρ (Set.Ico 0 b) :=
          setLIntegral_mono' measurableSet_Ico hpt
      _ = renewalMeasure ρ (Set.Ico 0 b) * ENNReal.ofReal b := by
          rw [setLIntegral_const, Real.volume_Ico, sub_zero]
  -- Step 2: back to real integrals
  have hRHS : renewalMeasure ρ (Set.Ico 0 b) * ENNReal.ofReal b ≠ ∞ :=
    ENNReal.mul_ne_top hUb ENNReal.ofReal_ne_top
  have hE1fin : ∫⁻ x in Set.Ico b (2 * b), ENNReal.ofReal (2 * b - x) ∂(renewalMeasure ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hRHS (le_trans le_self_add hEsum)
  have hE2fin : 2 * ∫⁻ x in Set.Ico 0 b, ENNReal.ofReal (2 * x - b) ∂(renewalMeasure ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hRHS (le_trans le_add_self hEsum)
  have hT : ∫ x in Set.Ico b (2 * b), (2 * b - x) ∂(renewalMeasure ρ)
      = (∫⁻ x in Set.Ico b (2 * b), ENNReal.ofReal (2 * b - x) ∂(renewalMeasure ρ)).toReal := by
    have hnn : 0 ≤ᵐ[(renewalMeasure ρ).restrict (Set.Ico b (2 * b))] fun x : ℝ => 2 * b - x :=
      ae_restrict_of_forall_mem measurableSet_Ico fun x hx => by
        simp only [Pi.zero_apply]; linarith [hx.2]
    exact integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop)
  have hC2 : ∫ x in Set.Ico 0 b, 2 * max (x - b / 2) 0 ∂(renewalMeasure ρ)
      = (∫⁻ x in Set.Ico 0 b, ENNReal.ofReal (2 * x - b) ∂(renewalMeasure ρ)).toReal := by
    have hnn : 0 ≤ᵐ[(renewalMeasure ρ).restrict (Set.Ico 0 b)]
        fun x : ℝ => 2 * max (x - b / 2) 0 :=
      ae_restrict_of_forall_mem measurableSet_Ico fun x _ => by
        simp only [Pi.zero_apply]; positivity
    rw [integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop)]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    rcases le_total (x - b / 2) 0 with hx | hx
    · rw [max_eq_right hx, mul_zero, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos (by linarith)]
    · rw [max_eq_left hx]
      congr 1
      ring
  have hTC : (∫ x in Set.Ico b (2 * b), (2 * b - x) ∂(renewalMeasure ρ))
      + 2 * ∫ x in Set.Ico 0 b, 2 * max (x - b / 2) 0 ∂(renewalMeasure ρ) ≤ M * b := by
    rw [hT, hC2]
    have h1 := ENNReal.toReal_mono hRHS hEsum
    rw [ENNReal.toReal_add hE1fin hE2fin, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hb.le, ← hM] at h1
    simpa using h1
  -- Step 3: the two fixed mirror centers
  have hiC : IntegrableOn (fun x : ℝ => max (x - b / 2) 0) (Set.Ico 0 b) (renewalMeasure ρ) :=
    intOn ρ hρ (by fun_prop) le_rfl
  have hiD : IntegrableOn (fun x : ℝ => max (b / 2 - x) 0) (Set.Ico 0 b) (renewalMeasure ρ) :=
    intOn ρ hρ (by fun_prop) le_rfl
  have hiA : IntegrableOn (fun x : ℝ => x) (Set.Ico 0 b) (renewalMeasure ρ) :=
    intOn ρ hρ continuous_id le_rfl
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ x in Set.Ico 0 b, x ∂(renewalMeasure ρ) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ x in Set.Ico 0 b, max (x - b / 2) 0 ∂(renewalMeasure ρ) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∫ x in Set.Ico 0 b, max (b / 2 - x) 0 ∂(renewalMeasure ρ) :=
    ⟨_, rfl⟩
  have hV0 : B * M ≤ h * A := by
    have := hB 0
    rwa [setIntegral_congr_fun measurableSet_Ico (g := fun x => h * x) (fun x hx => by
      simp only [zero_sub, sub_zero]
      rw [max_eq_right (by linarith [hx.1]), max_eq_left hx.1]
      ring), integral_const_mul, ← hA] at this
  have hVb : B * M ≤ p * D + h * C := by
    have := hB (b / 2)
    rwa [integral_add (hiD.const_mul p) (hiC.const_mul h), integral_const_mul,
      integral_const_mul, ← hC, ← hD] at this
  have hACD : A = C - D + b / 2 * M := by
    have e : ∫ x in Set.Ico 0 b, x ∂(renewalMeasure ρ)
        = ∫ x in Set.Ico 0 b, (max (x - b / 2) 0 - max (b / 2 - x) 0 + b / 2) ∂(renewalMeasure ρ) := by
      refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
      rcases le_total x (b / 2) with hx | hx
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have hiCD : IntegrableOn (fun x : ℝ => max (x - b / 2) 0 - max (b / 2 - x) 0) (Set.Ico 0 b)
        (renewalMeasure ρ) := hiC.sub hiD
    rw [hA, e, integral_add hiCD (integrableOn_const hUb), integral_sub hiC hiD,
      setIntegral_const, smul_eq_mul, measureReal_def, ← hM, ← hC, ← hD]
    ring
  have hTC' : (∫ x in Set.Ico b (2 * b), (2 * b - x) ∂(renewalMeasure ρ)) + 4 * C ≤ b * M := by
    rw [integral_const_mul, ← hC] at hTC
    linarith
  obtain ⟨T, hT'⟩ : ∃ T : ℝ, T = ∫ x in Set.Ico b (2 * b), (2 * b - x) ∂(renewalMeasure ρ) :=
    ⟨_, rfl⟩
  rw [← hT'] at hTC' ⊢
  have k1 := mul_le_mul_of_nonneg_left hV0 (by positivity : (0 : ℝ) ≤ 4 * p * p)
  have k2 := mul_le_mul_of_nonneg_left hVb (by positivity : (0 : ℝ) ≤ 4 * p * h)
  have k3 := mul_le_mul_of_nonneg_left hTC' (by positivity : (0 : ℝ) ≤ h * (h + p) * p)
  rw [hACD] at k1
  have key : h * (h + p) * (p * T + 4 * (p / h) * M * B)
      ≤ h * (h + p) * ((3 * (p / h) + 1) * (h * p / (h + p)) * b * M) := by
    have e1 : h * (h + p) * (p * T + 4 * (p / h) * M * B)
        = h * (h + p) * p * T + 4 * p * (h + p) * (B * M) := by
      field_simp
      try ring
    have e2 : h * (h + p) * ((3 * (p / h) + 1) * (h * p / (h + p)) * b * M)
        = (3 * p + h) * h * p * b * M := by
      field_simp
      try ring
    rw [e1, e2]
    linarith
  exact le_of_mul_le_mul_left key (by positivity)
