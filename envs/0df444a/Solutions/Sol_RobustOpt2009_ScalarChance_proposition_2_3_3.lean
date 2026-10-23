-- Prove2me | solution 1 for RobustOpt2009.ScalarChance.proposition_2_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:46:01.034348+00:00
-- url     : https://prove2.me/submissions/7285fd26-0aa8-4a13-89ea-9411cc60273c

import Mathlib
import Definitions.Def_RobustOpt2009_ScalarChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open RobustOpt2009.ScalarChance

theorem g79v_clip (w l : ℝ) (hl : 0 ≤ l) :
    |max (-l) (min w l)| ≤ l ∧
    (max (-l) (min w l)) ^ 2 = (min |w| l) ^ 2 ∧
    max (-l) (min w l) * w = |w| * min |w| l ∧
    |w - max (-l) (min w l)| = |w| - min |w| l := by
  rcases le_total l w with h1 | h1
  · have hw : 0 ≤ w := hl.trans h1
    rw [min_eq_right h1, max_eq_right (by linarith), abs_of_nonneg hw, min_eq_right h1,
      abs_of_nonneg hl, abs_of_nonneg (by linarith : 0 ≤ w - l)]
    refine ⟨le_rfl, rfl, by ring, rfl⟩
  · rw [min_eq_left h1]
    rcases le_total (-l) w with h2 | h2
    · rw [max_eq_right h2]
      have ha : |w| ≤ l := abs_le.mpr ⟨h2, h1⟩
      rw [min_eq_left ha, sub_self, abs_zero, sub_self, sq_abs]
      refine ⟨ha, rfl, ?_, rfl⟩
      rcases le_total 0 w with h | h
      · rw [abs_of_nonneg h]; try ring
      · rw [abs_of_nonpos h]; try ring
    · rw [max_eq_left h2]
      have hw : w ≤ 0 := by linarith
      rw [abs_of_nonpos hw, min_eq_right (by linarith), abs_neg, abs_of_nonneg hl,
        abs_of_nonpos (by linarith : w - -l ≤ 0)]
      refine ⟨le_rfl, by ring, by ring, by ring⟩

/-- explicit optimal dual certificate for the box ∩ ball support function -/
theorem g79v_cert {L : ℕ} (r : ℝ) (hr : 0 ≤ r) (w : Fin L → ℝ) :
    ∃ η p q : Fin L → ℝ, η ∈ boxBall r ∧ (∀ i, p i + q i = w i) ∧
      (∑ i, |p i|) + r * Real.sqrt (∑ i, (q i) ^ 2) = ∑ i, η i * w i := by
  set N := Real.sqrt (∑ i, (w i) ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hNsq : N ^ 2 = ∑ i, (w i) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases hc1 : ∀ i, r * |w i| ≤ N
  · -- scaled direction
    by_cases hN' : N = 0
    · refine ⟨0, 0, w, ⟨fun i => by simp, by simp [hr]⟩, fun i => by simp, ?_⟩
      rw [← hN, hN']; simp
    · have hNp : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hN')
      refine ⟨fun i => r / N * w i, 0, w, ⟨fun i => ?_, ?_⟩, fun i => by simp, ?_⟩
      · rw [abs_mul, abs_div, abs_of_nonneg hr, abs_of_pos hNp, div_mul_eq_mul_div,
          div_le_one hNp]; exact hc1 i
      · have : ∑ i, (r / N * w i) ^ 2 = r ^ 2 := by
          simp_rw [mul_pow]; rw [← Finset.mul_sum, ← hNsq]; field_simp
        rw [this, Real.sqrt_sq hr]
      · simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, zero_add]
        rw [← hN]
        have : ∑ i, r / N * w i * w i = r / N * ∑ i, (w i) ^ 2 := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
        rw [this, ← hNsq]; field_simp
  · push Not at hc1
    obtain ⟨i0, hi0⟩ := hc1
    set S2 : ℝ := ∑ i, (if w i = 0 then (0:ℝ) else 1) with hS2
    by_cases hc2 : S2 ≤ r ^ 2
    · -- sign vector
      set η : Fin L → ℝ := fun i => if 0 < w i then 1 else if w i < 0 then -1 else 0 with hη
      have hηw : ∀ i, η i * w i = |w i| := by
        intro i; simp only [hη]
        split_ifs with h1 h2
        · rw [abs_of_pos h1]; ring
        · rw [abs_of_neg h2]; ring
        · have : w i = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
          rw [this]; simp
      have hη2 : ∀ i, η i ^ 2 = if w i = 0 then 0 else 1 := by
        intro i; simp only [hη]
        by_cases h0 : w i = 0
        · simp [h0]
        · rcases lt_or_gt_of_ne h0 with h | h
          · simp [h, not_lt.mpr h.le, h0]
          · simp [h, h0]
      refine ⟨η, w, 0, ⟨fun i => ?_, ?_⟩, fun i => by simp, ?_⟩
      · simp only [hη]; split_ifs <;> norm_num
      · rw [show ∑ i, η i ^ 2 = S2 from Finset.sum_congr rfl fun i _ => hη2 i]
        calc Real.sqrt S2 ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hc2
          _ = r := Real.sqrt_sq hr
      · simp [hηw]
    · -- clipping with IVT
      push Not at hc2
      have hw0 : w i0 ≠ 0 := by
        intro h; rw [h, abs_zero, mul_zero] at hi0; linarith
      have hwpos : 0 < |w i0| := abs_pos.mpr hw0
      set c : ℝ → Fin L → ℝ := fun l i => max (-l) (min (w i) l) with hc
      set g : ℝ → ℝ := fun l => ∑ i, (c l i) ^ 2 - r ^ 2 * l ^ 2 with hg
      have hgc : Continuous g := by
        simp only [hg, hc]; fun_prop
      set l0 : ℝ := Finset.univ.inf' ⟨i0, Finset.mem_univ _⟩
        (fun i => if w i = 0 then |w i0| else |w i|) with hl0
      have hl0pos : 0 < l0 := by
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' ⟨i0, Finset.mem_univ _⟩
          (fun i => if w i = 0 then |w i0| else |w i|)
        rw [hl0, hi]
        split_ifs with h
        · exact hwpos
        · exact abs_pos.mpr h
      have hl0le : l0 ≤ |w i0| := by
        have := Finset.inf'_le (fun i => if w i = 0 then |w i0| else |w i|) (Finset.mem_univ i0)
        simp only [hw0, if_false] at this; exact this
      have hg0 : 0 ≤ g l0 := by
        have : ∀ i, (c l0 i) ^ 2 = l0 ^ 2 * (if w i = 0 then 0 else 1) := by
          intro i
          rw [(g79v_clip (w i) l0 hl0pos.le).2.1]
          split_ifs with h
          · rw [h]; simp [hl0pos.le]
          · have : l0 ≤ |w i| := by
              have := Finset.inf'_le (fun i => if w i = 0 then |w i0| else |w i|) (Finset.mem_univ i)
              simp only [h, if_false] at this; exact this
            rw [min_eq_right this]; ring
        simp only [hg]
        rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, ← hS2]
        nlinarith [sq_nonneg l0]
      have hg1 : g |w i0| ≤ 0 := by
        have hle : ∑ i, (c |w i0| i) ^ 2 ≤ ∑ i, (w i) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [(g79v_clip (w i) _ hwpos.le).2.1, ← sq_abs (w i)]
          exact pow_le_pow_left₀ (le_min (abs_nonneg _) hwpos.le) (min_le_left _ _) 2
        have : N ^ 2 < (r * |w i0|) ^ 2 := pow_lt_pow_left₀ hi0 hN0 two_ne_zero
        simp only [hg]; rw [mul_pow] at this; nlinarith
      obtain ⟨l, ⟨hl1, hl2⟩, hgl⟩ := intermediate_value_Icc' hl0le hgc.continuousOn ⟨hg1, hg0⟩
      have hlpos : 0 < l := lt_of_lt_of_le hl0pos hl1
      have hsq : ∑ i, (c l i) ^ 2 = r ^ 2 * l ^ 2 := by simp only [hg] at hgl; linarith
      refine ⟨fun i => c l i / l, fun i => w i - c l i, c l, ⟨fun i => ?_, ?_⟩, fun i => by ring, ?_⟩
      · rw [abs_div, abs_of_pos hlpos, div_le_one hlpos]; exact (g79v_clip (w i) l hlpos.le).1
      · have : ∑ i, (c l i / l) ^ 2 = r ^ 2 := by
          simp_rw [div_pow]; rw [← Finset.sum_div, hsq]; field_simp
        rw [this, Real.sqrt_sq hr]
      · rw [hsq, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr, Real.sqrt_sq hlpos.le]
        have e1 : ∀ i, |w i - c l i| = |w i| - min |w i| l := fun i => (g79v_clip (w i) l hlpos.le).2.2.2
        have e2 : ∀ i, c l i / l * w i = |w i| * min |w i| l / l := fun i => by
          rw [div_mul_eq_mul_div, (g79v_clip (w i) l hlpos.le).2.2.1]
        simp_rw [e1, e2]
        have hm2 : ∑ i, (min |w i| l) ^ 2 = r ^ 2 * l ^ 2 := by
          rw [← hsq]; exact Finset.sum_congr rfl fun i _ => ((g79v_clip (w i) l hlpos.le).2.1).symm
        have key : ∀ i, |w i| * min |w i| l = l * (|w i| - min |w i| l) + (min |w i| l) ^ 2 := by
          intro i
          rcases le_total |w i| l with h | h
          · rw [min_eq_left h]; ring
          · rw [min_eq_right h]; ring
        rw [← Finset.sum_div]
        simp_rw [key]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hm2]
        field_simp
        try ring
theorem g79v_231 {L : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (hmean : ∀ i, ∫ ω, ζ i ω ∂P = 0)
    (hbounded : ∀ i, ∀ᵐ ω ∂P, ζ i ω ∈ Set.Icc (-1 : ℝ) 1) (z : Fin L → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    P.real {ω | r * Real.sqrt (∑ i, (z i)^2) < ∑ i, z i * ζ i ω} ≤
      Real.exp (-(r^2 / 2)) := by
  set s := ∑ i, (z i) ^ 2 with hs
  by_cases hs0 : s = 0
  · have hz : ∀ i, z i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).1 hs0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have : {ω | r * Real.sqrt s < ∑ i, z i * ζ i ω} = ∅ := by
      ext ω; simp [hz, hs0]
    rw [this, measureReal_empty]
    positivity
  · have hspos : 0 < s := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hs0)
    have hsub := fun i => (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i).aemeasurable
        (hbounded i) (hmean i)).const_mul (z i)
    have hind : iIndepFun (fun i ω => z i * ζ i ω) P :=
      hindep.comp (fun i x => z i * x) (fun i => measurable_const.mul measurable_id)
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := Finset.univ)
      (fun i _ => hsub i) (ε := r * Real.sqrt s) (by positivity)
    calc P.real {ω | r * Real.sqrt s < ∑ i, z i * ζ i ω}
        ≤ P.real {ω | r * Real.sqrt s ≤ ∑ i, z i * ζ i ω} :=
          measureReal_mono (fun ω (hω : r * Real.sqrt s < _) => hω.le) (measure_ne_top _ _)
      _ ≤ _ := h
      _ = Real.exp (-(r ^ 2 / 2)) := by
          congr 1
          push_cast
          norm_num
          rw [mul_pow, Real.sq_sqrt hspos.le]
          change -(r ^ 2 * s) / (2 * ∑ x : Fin L, z x ^ 2 * 1) = -(r ^ 2 / 2)
          simp only [mul_one, ← hs]
          field_simp

theorem g79v_norm {L : ℕ} (v : Fin L → ℝ) :
    Real.sqrt (∑ i, v i ^ 2) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin L))‖ := by
  rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]

theorem g79v_tri {L : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (q q' : Fin L → ℝ) :
    Real.sqrt (∑ i, (a * q i + b * q' i) ^ 2) ≤
      a * Real.sqrt (∑ i, q i ^ 2) + b * Real.sqrt (∑ i, q' i ^ 2) := by
  rw [g79v_norm, g79v_norm q, g79v_norm q']
  have : (WithLp.toLp 2 (fun i => a * q i + b * q' i) : EuclideanSpace ℝ (Fin L)) =
      a • (WithLp.toLp 2 q : EuclideanSpace ℝ (Fin L)) + b • (WithLp.toLp 2 q' : EuclideanSpace ℝ (Fin L)) := by
    ext i; simp
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

theorem solution {L n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) :
    (∀ x, RobustFeasible (boxBall r) (residual a0 b0 a b x) ↔
      ∃ p q, BoxBallSystem r (residual a0 b0 a b x) p q) ∧
    (∀ {S : Type} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
      (ζ : Fin L → S → ℝ), (∀ i, Measurable (ζ i)) → iIndepFun ζ P →
      (∀ i, ∫ ω, ζ i ω ∂P = 0) →
      (∀ i, ∀ᵐ ω ∂P, ζ i ω ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ x p q, BoxBallSystem r (residual a0 b0 a b x) p q →
        violation P ζ (residual a0 b0 a b x) ≤ Real.exp (-(r^2 / 2))) ∧
    Convex ℝ {t : (Fin n → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) |
      BoxBallSystem r (residual a0 b0 a b t.1) t.2.1 t.2.2} := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · obtain ⟨z1, y⟩ := residual a0 b0 a b x
    constructor
    · intro h
      obtain ⟨η, p, q, hη, hpq, heq⟩ := g79v_cert r hr (fun i => -y i)
      refine ⟨p, q, fun i => hpq i, ?_⟩
      have hneg : (fun i => -η i) ∈ boxBall r := by
        refine ⟨fun i => by rw [abs_neg]; exact hη.1 i, ?_⟩
        simp only [neg_sq]; exact hη.2
      have := h _ hneg
      simp only at this ⊢
      have e : ∑ i, η i * -y i = ∑ i, -η i * y i := Finset.sum_congr rfl fun i _ => by ring
      rw [heq, e]; linarith
    · rintro ⟨p, q, hpq, hle⟩ η hη
      simp only at hpq hle ⊢
      have e : ∑ i, η i * y i = ∑ i, (-η i * p i) + ∑ i, (-η i) * q i := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        have := hpq i; linear_combination (η i) * this
      have h1 : ∑ i, (-η i * p i) ≤ ∑ i, |p i| := Finset.sum_le_sum fun i _ => by
        calc -η i * p i ≤ |-η i * p i| := le_abs_self _
          _ = |η i| * |p i| := by rw [abs_mul, abs_neg]
          _ ≤ 1 * |p i| := mul_le_mul_of_nonneg_right (hη.1 i) (abs_nonneg _)
          _ = |p i| := one_mul _
      have h2 : ∑ i, (-η i) * q i ≤ r * Real.sqrt (∑ i, q i ^ 2) := by
        refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
        simp only [neg_sq]
        exact mul_le_mul_of_nonneg_right hη.2 (Real.sqrt_nonneg _)
      rw [e]; linarith
  · intro S _ P _ ζ hmeas hindep hmean hbd x p q hsys
    generalize residual a0 b0 a b x = z at hsys ⊢
    obtain ⟨z1, y⟩ := z
    obtain ⟨hpq, hle⟩ := hsys
    have hall : ∀ᵐ ω ∂P, ∀ i, ζ i ω ∈ Set.Icc (-1 : ℝ) 1 := ae_all_iff.2 hbd
    have hsub : {ω | 0 < z1 + ∑ i, ζ i ω * y i} ≤ᵐ[P]
        {ω | r * Real.sqrt (∑ i, (-q i) ^ 2) < ∑ i, (-q i) * ζ i ω} := by
      filter_upwards [hall] with ω hω
      intro hpos
      change 0 < z1 + ∑ i, ζ i ω * y i at hpos
      change r * Real.sqrt (∑ i, (-q i) ^ 2) < ∑ i, (-q i) * ζ i ω
      have e : ∑ i, ζ i ω * y i = ∑ i, (-ζ i ω * p i) + ∑ i, (-q i) * ζ i ω := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        have := hpq i; linear_combination (ζ i ω) * this
      have h1 : ∑ i, (-ζ i ω * p i) ≤ ∑ i, |p i| := Finset.sum_le_sum fun i _ => by
        have hz : |ζ i ω| ≤ 1 := abs_le.mpr (hω i)
        calc -ζ i ω * p i ≤ |-ζ i ω * p i| := le_abs_self _
          _ = |ζ i ω| * |p i| := by rw [abs_mul, abs_neg]
          _ ≤ 1 * |p i| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
          _ = |p i| := one_mul _
      simp only [neg_sq]
      linarith
    have := g79v_231 P ζ hmeas hindep hmean hbd (fun i => -q i) r hr
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans this
  · rintro ⟨x, p, q⟩ ⟨hpq, hle⟩ ⟨x', p', q'⟩ ⟨hpq', hle'⟩ s t hs ht hst
    have hsum : ∀ c : Fin n → ℝ, ∑ j, c j * (s * x j + t * x' j) =
        s * ∑ j, c j * x j + t * ∑ j, c j * x' j := by
      intro c
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    simp only [RobustOpt2009.ScalarChance.residual] at hpq hle hpq' hle' ⊢
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum]
      have h1 := hpq i; have h2 := hpq' i
      linear_combination s * h1 + t * h2 + b i * hst
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum]
      have ha : ∑ i, |s * p i + t * p' i| ≤ s * ∑ i, |p i| + t * ∑ i, |p' i| := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      have hb := g79v_tri s t hs ht q q'
      calc _ ≤ (s * ∑ i, |p i| + t * ∑ i, |p' i|) +
            r * (s * Real.sqrt (∑ i, q i ^ 2) + t * Real.sqrt (∑ i, q' i ^ 2)) :=
            add_le_add ha (mul_le_mul_of_nonneg_left hb hr)
        _ = s * (∑ i, |p i| + r * Real.sqrt (∑ i, q i ^ 2)) +
            t * (∑ i, |p' i| + r * Real.sqrt (∑ i, q' i ^ 2)) := by ring
        _ ≤ s * (-(∑ j, a0 j * x j - b0)) + t * (-(∑ j, a0 j * x' j - b0)) :=
            add_le_add (mul_le_mul_of_nonneg_left hle hs) (mul_le_mul_of_nonneg_left hle' ht)
        _ = _ := by linear_combination b0 * hst
