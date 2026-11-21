-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:14:34.258829+00:00
-- url     : https://prove2.me/submissions/84ab1f5b-74bb-4e48-a78c-231a44292f7a

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
import Definitions.Def_HighDimProb_Chaining_VcDim

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

end OptimalAgnosticPAC.Dev.T3
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L32
open OptimalAgnosticPAC.Learner

theorem sum_succ {Z : Type} (w : (t : ℕ) → (Fin t → Z) → Z → ℝ) (m : ℕ) (S : Fin (m + 1) → Z) :
    ∑ t : Fin (m + 1), w t (prefixSample S t t.isLt.le) (S t) =
      ∑ t : Fin m, w t (prefixSample (fun i : Fin m => S (Fin.castSucc i)) t t.isLt.le)
        (S (Fin.castSucc t)) + w m (fun i : Fin m => S (Fin.castSucc i)) (S (Fin.last m)) := by
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem measurable_sum {Z : Type} [MeasurableSpace Z] (w : (t : ℕ) → (Fin t → Z) → Z → ℝ)
    (hw : ∀ t, Measurable (fun p : (Fin t → Z) × Z => w t p.1 p.2)) (m : ℕ) :
    Measurable (fun S : Fin m → Z => ∑ t : Fin m, w t (prefixSample S t t.isLt.le) (S t)) := by
  refine Finset.measurable_sum _ (fun t _ => ?_)
  have h1 : Measurable (fun S : Fin m → Z => (prefixSample S t t.isLt.le, S t)) := by
    refine Measurable.prodMk ?_ (measurable_pi_apply _)
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  exact (hw t).comp h1

/-- Iterated conditional exponential bound. -/
theorem exp_sum_le {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (w : (t : ℕ) → (Fin t → Z) → Z → ℝ)
    (hw : ∀ t, Measurable (fun p : (Fin t → Z) × Z => w t p.1 p.2))
    (h1 : ∀ t s, ∫⁻ z, ENNReal.ofReal (Real.exp (w t s z)) ∂P ≤ 1) (m : ℕ) :
    ∫⁻ S, ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample S t t.isLt.le) (S t)))
      ∂(Measure.pi (fun _ : Fin m => P)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    set μ : Measure (Fin (m + 1) → Z) := Measure.pi (fun _ : Fin (m + 1) => P) with hμ
    set μm : Measure (Fin m → Z) := Measure.pi (fun _ : Fin m => P) with hμm
    set F : (Fin (m + 1) → Z) → ENNReal := fun S =>
      ENNReal.ofReal (Real.exp (∑ t : Fin (m + 1), w t (prefixSample S t t.isLt.le) (S t))) with hF
    have hFm : Measurable F :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_sum w hw (m + 1))))
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => P) (Fin.last m)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Z) (Fin.last m) with he
    have step1 : ∫⁻ S, F S ∂μ = ∫⁻ p, F (e.symm p) ∂(P.prod μm) := by
      have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => F (e.symm p))
      simp only [MeasurableEquiv.symm_apply_apply] at this
      rw [this]
    have hFe : Measurable (fun p => F (e.symm p)) := hFm.comp e.symm.measurable
    have hsy : ∀ (z : Z) (s : Fin m → Z), (∀ i : Fin m, (e.symm (z, s)) (Fin.castSucc i) = s i) ∧
        (e.symm (z, s)) (Fin.last m) = z := by
      intro z s
      refine ⟨?_, ?_⟩
      · intro i
        have : Fin.castSucc i = (Fin.last m).succAbove i := by
          rw [Fin.succAbove_last]
        rw [this]
        simp [he, MeasurableEquiv.piFinSuccAbove]
      · simp [he, MeasurableEquiv.piFinSuccAbove]
    have hFs : ∀ (z : Z) (s : Fin m → Z), F (e.symm (z, s)) =
        ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample s t t.isLt.le) (s t))) *
          ENNReal.ofReal (Real.exp (w m s z)) := by
      intro z s
      obtain ⟨h1', h2'⟩ := hsy z s
      simp only [hF]
      rw [sum_succ]
      simp only [h1', h2', Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [step1, lintegral_prod_symm _ hFe.aemeasurable]
    calc ∫⁻ s, ∫⁻ z, F (e.symm (z, s)) ∂P ∂μm
        ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample s t t.isLt.le) (s t))) ∂μm := by
          refine lintegral_mono (fun s => ?_)
          simp only [hFs]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc _ ≤ ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample s t t.isLt.le) (s t))) * 1 :=
                by gcongr; exact h1 m s
            _ = _ := mul_one _
      _ ≤ 1 := ih
end OptimalAgnosticPAC.Dev.L32
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L32

theorem exp_le_quad (x : ℝ) (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + (3 / 4) * x ^ 2 := by
  have h := Real.exp_bound (x := x) hx (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.factorial] at h
  have h3 : |x| ^ 3 ≤ x ^ 2 := by
    have : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [this]
    nlinarith [sq_nonneg x, abs_nonneg x]
  have := (abs_le.mp h).2
  nlinarith [sq_nonneg x]

theorem bern {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (l I : Z → ℝ) (hl : Measurable l) (hI : Measurable I)
    (hl0 : ∀ z, 0 ≤ l z) (hl1 : ∀ z, l z ≤ 1) (hI0 : ∀ z, 0 ≤ I z) (hI1 : ∀ z, I z ≤ 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 2) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (lam * (((∫ z, l z ∂P) - ∫ z, I z ∂P - (l z - I z)) -
      (3 * lam / 4) * ((∫ z, l z ∂P) + ∫ z, I z ∂P)))) ∂P ≤ 1 := by
  set Lq := ∫ z, l z ∂P with hLq
  set Lh := ∫ z, I z ∂P with hLh
  have hlint : Integrable l P := Integrable.of_bound hl.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hl0 z)]; exact hl1 z))
  have hIint : Integrable I P := Integrable.of_bound hI.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hI0 z)]; exact hI1 z))
  have hLq0 : 0 ≤ Lq := integral_nonneg hl0
  have hLh0 : 0 ≤ Lh := integral_nonneg hI0
  have hLq1 : Lq ≤ 1 := by
    have := integral_mono hlint (integrable_const (1 : ℝ)) (fun z => hl1 z)
    simpa using this
  have hLh1 : Lh ≤ 1 := by
    have := integral_mono hIint (integrable_const (1 : ℝ)) (fun z => hI1 z)
    simpa using this
  set a := Lq - Lh with ha
  set K := Real.exp (-(lam * (3 * lam / 4) * (Lq + Lh))) with hK
  set c0 := 1 + lam * a + (3 / 4) * lam ^ 2 * a ^ 2 with hc0
  set c1 := -lam - (3 / 2) * lam ^ 2 * a + (3 / 4) * lam ^ 2 with hc1
  set c2 := lam + (3 / 2) * lam ^ 2 * a + (3 / 4) * lam ^ 2 with hc2
  have hpt : ∀ z, Real.exp (lam * ((a - (l z - I z)) - (3 * lam / 4) * (Lq + Lh))) ≤
      K * (c0 + c1 * l z + c2 * I z) := by
    intro z
    have hx : |lam * (a - (l z - I z))| ≤ 1 := by
      rw [abs_le]
      have := hl0 z; have := hl1 z; have := hI0 z; have := hI1 z
      constructor <;> nlinarith
    have h1 := exp_le_quad _ hx
    have hsplit : lam * ((a - (l z - I z)) - (3 * lam / 4) * (Lq + Lh)) =
        lam * (a - (l z - I z)) + (-(lam * (3 * lam / 4) * (Lq + Lh))) := by ring
    rw [hsplit, Real.exp_add, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine h1.trans ?_
    have hd : (l z - I z) ^ 2 ≤ l z + I z := by
      have := hl0 z; have := hl1 z; have := hI0 z; have := hI1 z
      nlinarith [mul_nonneg (hl0 z) (hI0 z), mul_nonneg (hl0 z) (sub_nonneg.mpr (hl1 z)),
        mul_nonneg (hI0 z) (sub_nonneg.mpr (hI1 z))]
    have : (3 / 4) * (lam * (a - (l z - I z))) ^ 2 ≤
        (3 / 4) * lam ^ 2 * (a ^ 2 - 2 * a * (l z - I z) + (l z + I z)) := by
      have : (a - (l z - I z)) ^ 2 ≤ a ^ 2 - 2 * a * (l z - I z) + (l z + I z) := by nlinarith
      have h2 : (lam * (a - (l z - I z))) ^ 2 = lam ^ 2 * (a - (l z - I z)) ^ 2 := by ring
      rw [h2]
      nlinarith [sq_nonneg lam]
    have e : c0 + c1 * l z + c2 * I z = 1 + lam * (a - (l z - I z)) +
        (3 / 4) * lam ^ 2 * (a ^ 2 - 2 * a * (l z - I z) + (l z + I z)) := by
      simp only [hc0, hc1, hc2]; ring
    rw [e]; linarith
  have hBint : Integrable (fun z => K * (c0 + c1 * l z + c2 * I z)) P := by
    refine Integrable.const_mul ?_ K
    exact ((integrable_const c0).add (hlint.const_mul c1)).add (hIint.const_mul c2)
  have hBval : ∫ z, K * (c0 + c1 * l z + c2 * I z) ∂P = K * (c0 + c1 * Lq + c2 * Lh) := by
    rw [integral_const_mul]
    congr 1
    have i1 : Integrable (fun z => c0 + c1 * l z) P := (integrable_const c0).add (hlint.const_mul c1)
    have i2 : Integrable (fun z => c2 * I z) P := hIint.const_mul c2
    rw [integral_add i1 i2, integral_add (integrable_const c0) (hlint.const_mul c1),
      integral_const_mul, integral_const_mul]
    simp [hLq, hLh]
  have hKpos : 0 < K := Real.exp_pos _
  have hpos : ∀ z, 0 ≤ K * (c0 + c1 * l z + c2 * I z) := fun z =>
    (Real.exp_pos _).le.trans (hpt z)
  have hmain : K * (c0 + c1 * Lq + c2 * Lh) ≤ 1 := by
    have e1 : c0 + c1 * Lq + c2 * Lh = 1 + (3 / 4) * lam ^ 2 * (Lq + Lh - a ^ 2) := by
      simp only [hc0, hc1, hc2, ha]; ring
    have h2 : c0 + c1 * Lq + c2 * Lh ≤ 1 + lam * (3 * lam / 4) * (Lq + Lh) := by
      rw [e1]; nlinarith [sq_nonneg a, sq_nonneg lam]
    have h3 : 1 + lam * (3 * lam / 4) * (Lq + Lh) ≤ Real.exp (lam * (3 * lam / 4) * (Lq + Lh)) := by
      linarith [Real.add_one_le_exp (lam * (3 * lam / 4) * (Lq + Lh))]
    have h4 : K * Real.exp (lam * (3 * lam / 4) * (Lq + Lh)) = 1 := by
      rw [hK, ← Real.exp_add]; simp
    calc K * (c0 + c1 * Lq + c2 * Lh) ≤ K * Real.exp (lam * (3 * lam / 4) * (Lq + Lh)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hKpos.le
      _ = 1 := h4
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (lam * ((a - (l z - I z)) - (3 * lam / 4) * (Lq + Lh)))) ∂P
      ≤ ∫⁻ z, ENNReal.ofReal (K * (c0 + c1 * l z + c2 * I z)) ∂P :=
        lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hpt z))
    _ = ENNReal.ofReal (∫ z, K * (c0 + c1 * l z + c2 * I z) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hBint (Filter.Eventually.of_forall hpos)).symm
    _ ≤ 1 := by
        rw [hBval]
        exact ENNReal.ofReal_le_one.mpr hmain
end OptimalAgnosticPAC.Dev.L32
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L32

theorem card_suffix (k : ℕ) :
    (Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val)).card = k := by
  rw [← Finset.card_map Fin.valEmbedding]
  have : (Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val)).map Fin.valEmbedding =
      Finset.Ico k (2 * k) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨ht, t.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  rw [this]; simp; omega

theorem lam_choice (L ℓ kR : ℝ) (hL : 0 ≤ L) (hℓ : 0 < ℓ) (hk : 0 < kR) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 / 2 ∧
      3 * lam * L + 2 * ℓ / (lam * kR) ≤ 5 * Real.sqrt (L * ℓ / kR) + 10 * ℓ / kR := by
  rcases hL.eq_or_lt with h0 | hpos
  · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    rw [← h0]
    have : 2 * ℓ / (1 / 2 * kR) = 4 * ℓ / kR := by field_simp; ring
    rw [this]
    have h1 : 0 ≤ Real.sqrt (0 * ℓ / kR) := Real.sqrt_nonneg _
    have h2 : 4 * ℓ / kR ≤ 10 * ℓ / kR := by
      apply div_le_div_of_nonneg_right _ hk.le; linarith
    linarith
  · set s := Real.sqrt (ℓ / (kR * L)) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = ℓ / (kR * L) := Real.sq_sqrt (by positivity)
    have hsq : Real.sqrt (L * ℓ / kR) = L * s := by
      rw [show L * ℓ / kR = (L * s) ^ 2 by rw [mul_pow, hs2]; field_simp]
      exact Real.sqrt_sq (by positivity)
    by_cases hc : s ≤ 1 / 2
    · refine ⟨s, hspos, hc, ?_⟩
      rw [hsq]
      have e1 : 2 * ℓ / (s * kR) = 2 * (L * s) := by
        have : ℓ = s ^ 2 * (kR * L) := by rw [hs2]; field_simp
        rw [this]; field_simp
      rw [e1]
      have : 0 ≤ 10 * ℓ / kR := by positivity
      nlinarith
    · push Not at hc
      refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
      rw [hsq]
      have hL4 : L ≤ 4 * ℓ / kR := by
        have : ℓ = s ^ 2 * (kR * L) := by rw [hs2]; field_simp
        rw [le_div_iff₀ hk]
        have : 1 / 4 < s ^ 2 := by nlinarith
        nlinarith [mul_pos hk hpos]
      have e1 : 2 * ℓ / (1 / 2 * kR) = 4 * ℓ / kR := by field_simp; ring
      rw [e1]
      have : 0 ≤ L * s := by positivity
      have h5 : 3 * (1 / 2) * L ≤ 6 * ℓ / kR := by
        have : 6 * ℓ / kR = (3 / 2) * (4 * ℓ / kR) := by ring
        rw [this]; nlinarith
      have h6 : 4 * ℓ / kR + 6 * ℓ / kR = 10 * ℓ / kR := by ring
      nlinarith

theorem bad_imp (A D L ℓ kR lam sq : ℝ) (hk : 0 < kR) (hlam : 0 < lam) (hlam1 : lam ≤ 1 / 2)
    (hL : 0 ≤ L) (hℓ : 0 < ℓ)
    (hlc : 3 * lam * L + 2 * ℓ / (lam * kR) ≤ 5 * sq + 10 * ℓ / kR)
    (hbad : (2 / kR) * max D 0 + 5 * sq + 10 * (ℓ / kR) < (1 / kR) * A) :
    ℓ < lam * ((A - D) - (3 * lam / 4) * (A + 2 * kR * L)) := by
  set m := max D 0 with hm
  have hmD : D ≤ m := le_max_left _ _
  have hm0 : 0 ≤ m := le_max_right _ _
  have h1 : (2 / kR) * m + 3 * lam * L + 2 * ℓ / (lam * kR) < (1 / kR) * A := by
    have : 10 * (ℓ / kR) = 10 * ℓ / kR := by ring
    linarith
  have h2 := mul_lt_mul_of_pos_left h1 (mul_pos hk hlam)
  have e : kR * lam * ((2 / kR) * m + 3 * lam * L + 2 * ℓ / (lam * kR)) =
      2 * m * lam + 3 * lam ^ 2 * kR * L + 2 * ℓ := by field_simp
  have e2 : kR * lam * ((1 / kR) * A) = lam * A := by field_simp
  rw [e, e2] at h2
  have hc : 3 * lam / 4 ≤ 3 / 8 := by linarith
  have hc1 : 0 < 1 - 3 * lam / 4 := by linarith
  have h3 := mul_lt_mul_of_pos_left h2 hc1
  have hLk : 0 ≤ lam * kR * L := by positivity
  have hlL : 0 ≤ lam ^ 2 * (kR * L) := by positivity
  nlinarith [mul_nonneg hm0 hlam.le, mul_nonneg (sub_nonneg.mpr hmD) hlam.le,
    mul_nonneg hlL (by linarith : (0:ℝ) ≤ 3 / 2 - 9 * lam / 4), mul_nonneg hℓ.le hc1.le,
    mul_nonneg (mul_nonneg hm0 hlam.le) (by linarith : (0:ℝ) ≤ 1 - 2 * (3 * lam / 4)),
    mul_nonneg hℓ.le (by linarith : (0:ℝ) ≤ 1 - 2 * (3 * lam / 4))]
end OptimalAgnosticPAC.Dev.L32
end

section
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Dev.L32
open OptimalAgnosticPAC.Learner

/-- the increment of the exponential supermartingale -/
noncomputable def wInc {X : Type} [MeasurableSpace X]
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (P : Measure (X × Bool)) (h : X → Bool)
    (k : ℕ) (lam : ℝ) (t : ℕ) (s : Fin t → X × Bool) (z : X × Bool) : ℝ :=
  if k ≤ t then
    lam * (((scoreRisk P (q t s) - risk P h) -
      (loss (q t s z.1) z.2 - (if h z.1 ≠ z.2 then 1 else 0))) -
      (3 * lam / 4) * (scoreRisk P (q t s) + risk P h))
  else 0

theorem loss_mem (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (y : Bool) : 0 ≤ loss a y ∧ loss a y ≤ 1 := by
  rw [T3.loss_eq a ha y]
  obtain ⟨h1, h2⟩ := ha
  unfold sgn
  split_ifs <;> constructor <;> linarith

theorem meas_joint {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q) (t : ℕ) :
    Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => loss (q t p.1 p.2.1) p.2.2) := by
  unfold loss
  have h1 : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => sgn p.2.2) :=
    (measurable_from_top (f := sgn)).comp (measurable_snd.comp measurable_snd)
  have h2 : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => q t p.1 p.2.1) :=
    (hq.measurable t).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact ((h2.sub h1).abs).div_const 2

theorem meas_ind {X : Type} [MeasurableSpace X] (h : X → Bool) (hh : Measurable h) :
    MeasurableSet {z : X × Bool | h z.1 ≠ z.2} := by
  have : MeasurableSet {z : X × Bool | h z.1 = z.2} :=
    measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd
  exact this.compl

theorem wInc_meas {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : X → Bool) (hh : Measurable h)
    (k : ℕ) (lam : ℝ) (t : ℕ) :
    Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => wInc q P h k lam t p.1 p.2) := by
  unfold wInc
  by_cases hkt : k ≤ t
  · simp only [hkt, if_true]
    have hsr : Measurable (fun s : Fin t → X × Bool => scoreRisk P (q t s)) := by
      unfold scoreRisk
      exact (StronglyMeasurable.integral_prod_right' (f := fun p : (Fin t → X × Bool) × (X × Bool) =>
        loss (q t p.1 p.2.1) p.2.2) (meas_joint H d q hq t).stronglyMeasurable).measurable
    have hsr' : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => scoreRisk P (q t p.1)) :=
      hsr.comp measurable_fst
    have hI : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) =>
        (if h p.2.1 ≠ p.2.2 then (1 : ℝ) else 0)) :=
      Measurable.ite ((meas_ind h hh).preimage measurable_snd) measurable_const measurable_const
    refine Measurable.const_mul ?_ lam
    exact (((hsr'.sub measurable_const).sub ((meas_joint H d q hq t).sub hI)).sub
      ((hsr'.add measurable_const).const_mul _))
  · simp only [hkt, if_false]; exact measurable_const

theorem wInc_int {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : X → Bool) (hh : Measurable h)
    (k : ℕ) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 2) (t : ℕ) (s : Fin t → X × Bool) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (wInc q P h k lam t s z)) ∂P ≤ 1 := by
  by_cases hkt : k ≤ t
  · have hqs : Measurable (q t s) := (hq.measurable t).comp (measurable_prodMk_left)
    have hl := T3.measurable_loss (q t s) hqs
    have hI : Measurable (fun z : X × Bool => (if h z.1 ≠ z.2 then (1 : ℝ) else 0)) :=
      Measurable.ite (meas_ind h hh) measurable_const measurable_const
    have hrisk : risk P h = ∫ z, (if h z.1 ≠ z.2 then (1 : ℝ) else 0) ∂P := by
      have : (fun z : X × Bool => (if h z.1 ≠ z.2 then (1 : ℝ) else 0)) =
          Set.indicator {z : X × Bool | h z.1 ≠ z.2} 1 := by
        funext z; by_cases hz : h z.1 ≠ z.2 <;> simp [hz]
      rw [this, integral_indicator_one (meas_ind h hh)]; rfl
    have key := bern P (fun z => loss (q t s z.1) z.2) (fun z => (if h z.1 ≠ z.2 then (1 : ℝ) else 0))
      hl hI (fun z => (loss_mem _ (hq.mem_Icc t s z.1) z.2).1)
      (fun z => (loss_mem _ (hq.mem_Icc t s z.1) z.2).2)
      (fun z => by split_ifs <;> norm_num) (fun z => by split_ifs <;> norm_num) lam hlam0 hlam1
    unfold wInc
    simp only [hkt, if_true]
    rw [hrisk]
    exact key
  · unfold wInc
    simp [hkt]

end OptimalAgnosticPAC.Dev.L32

namespace OptimalAgnosticPAC.Learner
open OptimalAgnosticPAC.Dev.L32

theorem chk_lemma_3_2 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) (h : X → Bool) (hh : h ∈ H)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    sampleLaw P (2 * k)
      {S | (2 / (k : ℝ)) * max (excessLossSum q h k S) 0 +
            5 * Real.sqrt (risk P h * Real.log (1 / δ) / (k : ℝ)) +
            10 * (Real.log (1 / δ) / (k : ℝ)) <
          (1 / (k : ℝ)) *
            ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
              (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h)} ≤
      ENNReal.ofReal δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓ : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ0]; linarith
  have hL0 : 0 ≤ risk P h := measureReal_nonneg
  obtain ⟨lam, hlam0, hlam1, hlc⟩ := lam_choice (risk P h) (Real.log (1 / δ)) k hL0 hℓ hkR
  have hexp := exp_sum_le P (wInc q P h k lam) (wInc_meas H d q hq P h (hmeas h hh) k lam)
    (wInc_int H d q hq P h (hmeas h hh) k lam hlam0 hlam1) (2 * k)
  set G : (Fin (2 * k) → X × Bool) → ℝ := fun S =>
    ∑ t : Fin (2 * k), wInc q P h k lam t (prefixSample S t t.isLt.le) (S t) with hG
  have hGeq : ∀ S : Fin (2 * k) → X × Bool, G S =
      lam * (((∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
              (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h)) -
          excessLossSum q h k S) -
        (3 * lam / 4) * ((∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
              (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h)) +
          2 * (k : ℝ) * risk P h)) := by
    intro S
    simp only [hG, wInc]
    rw [← Finset.sum_filter]
    unfold excessLossSum excessLoss
    have hc := card_suffix k
    have e : ∀ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
        lam * (((scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h) -
          (loss (q t (prefixSample S t t.isLt.le) (S t).1) (S t).2 -
            (if h (S t).1 ≠ (S t).2 then 1 else 0))) -
          (3 * lam / 4) * (scoreRisk P (q t (prefixSample S t t.isLt.le)) + risk P h)) =
        lam * (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h) -
          lam * (loss (q t (prefixSample S t t.isLt.le) (S t).1) (S t).2 -
            (if h (S t).1 ≠ (S t).2 then 1 else 0)) -
          (3 * lam / 4) * lam * (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h) -
          (3 * lam / 4) * lam * (2 * risk P h) := by
      intros; ring
    rw [Finset.sum_congr rfl e]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hc, nsmul_eq_mul]
    ring
  have hGm : Measurable G := measurable_sum _ (wInc_meas H d q hq P h (hmeas h hh) k lam) (2 * k)
  have hFm : Measurable (fun S => ENNReal.ofReal (Real.exp (G S))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hGm)
  set ε : ENNReal := ENNReal.ofReal (1 / δ) with hε
  have hsub : {S : Fin (2 * k) → X × Bool | (2 / (k : ℝ)) * max (excessLossSum q h k S) 0 +
            5 * Real.sqrt (risk P h * Real.log (1 / δ) / (k : ℝ)) +
            10 * (Real.log (1 / δ) / (k : ℝ)) <
          (1 / (k : ℝ)) *
            ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
              (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h)} ⊆
      {S | ε ≤ ENNReal.ofReal (Real.exp (G S))} := by
    intro S hS
    have hb := bad_imp _ _ _ _ _ _ _ hkR hlam0 hlam1 hL0 hℓ hlc (by
      have := hS
      simp only [Set.mem_setOf_eq] at this
      linarith)
    rw [← hGeq S] at hb
    simp only [Set.mem_setOf_eq, hε]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_log (show 0 < 1 / δ by positivity)]
    exact (Real.exp_lt_exp.mpr hb).le
  have hmk := mul_meas_ge_le_lintegral₀ (μ := Measure.pi (fun _ : Fin (2 * k) => P))
    hFm.aemeasurable ε
  have hmk' : ε * (Measure.pi (fun _ : Fin (2 * k) => P))
      {S | ε ≤ ENNReal.ofReal (Real.exp (G S))} ≤ 1 := hmk.trans hexp
  unfold sampleLaw
  refine (measure_mono hsub).trans ?_
  have hεδ : ENNReal.ofReal δ * ε = 1 := by
    rw [hε, ← ENNReal.ofReal_mul hδ0.le]
    rw [mul_one_div_cancel hδ0.ne']; simp
  calc (Measure.pi (fun _ : Fin (2 * k) => P)) {S | ε ≤ ENNReal.ofReal (Real.exp (G S))}
      = ENNReal.ofReal δ * (ε * (Measure.pi (fun _ : Fin (2 * k) => P))
          {S | ε ≤ ENNReal.ofReal (Real.exp (G S))}) := by
        rw [← mul_assoc, hεδ, one_mul]
    _ ≤ ENNReal.ofReal δ * 1 := by gcongr
    _ = _ := mul_one _
end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_lemma_3_2 := @OptimalAgnosticPAC.Learner.chk_lemma_3_2
