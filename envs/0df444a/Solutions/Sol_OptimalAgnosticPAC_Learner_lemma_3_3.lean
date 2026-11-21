-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:52:01.900966+00:00
-- url     : https://prove2.me/submissions/edb576e1-cdb6-4a73-992a-73bb5bed7e1e

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
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
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Dev.L33
open OptimalAgnosticPAC.Learner

/-- Single-pair Bernstein/Chernoff tail bound for an i.i.d. sample (relative deviation). -/
theorem tail {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (l I : Z → ℝ) (hl : Measurable l) (hI : Measurable I)
    (hl0 : ∀ z, 0 ≤ l z) (hl1 : ∀ z, l z ≤ 1) (hI0 : ∀ z, 0 ≤ I z) (hI1 : ∀ z, I z ≤ 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 2) (k : ℕ) (ℓ : ℝ) :
    Measure.pi (fun _ : Fin k => P)
      {S | ℓ ≤ ∑ i : Fin k, lam * (((∫ z, l z ∂P) - ∫ z, I z ∂P - (l (S i) - I (S i))) -
        (3 * lam / 4) * ((∫ z, l z ∂P) + ∫ z, I z ∂P))} ≤ ENNReal.ofReal (Real.exp (-ℓ)) := by
  set μ := Measure.pi (fun _ : Fin k => P) with hμ
  set w : (t : ℕ) → (Fin t → Z) → Z → ℝ := fun t _ z =>
    lam * (((∫ z, l z ∂P) - ∫ z, I z ∂P - (l z - I z)) -
        (3 * lam / 4) * ((∫ z, l z ∂P) + ∫ z, I z ∂P)) with hw
  have hwm : ∀ t, Measurable (fun p : (Fin t → Z) × Z => w t p.1 p.2) := fun t => by
    simp only [hw]
    exact measurable_const.mul ((measurable_const.sub ((hl.comp measurable_snd).sub
      (hI.comp measurable_snd))).sub measurable_const)
  have h1 := L32.exp_sum_le P w hwm (fun t s => L32.bern P l I hl hI hl0 hl1 hI0 hI1 lam hlam0 hlam1) k
  have hmeas : Measurable (fun S : Fin k → Z => ENNReal.ofReal (Real.exp
      (∑ t : Fin k, w t (prefixSample S t t.isLt.le) (S t)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (L32.measurable_sum w hwm k))
  have hsub : {S : Fin k → Z | ℓ ≤ ∑ i : Fin k, lam * (((∫ z, l z ∂P) - ∫ z, I z ∂P - (l (S i) - I (S i))) -
        (3 * lam / 4) * ((∫ z, l z ∂P) + ∫ z, I z ∂P))} ⊆
      {S | ENNReal.ofReal (Real.exp ℓ) ≤ ENNReal.ofReal (Real.exp
      (∑ t : Fin k, w t (prefixSample S t t.isLt.le) (S t)))} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hS)
  calc μ _ ≤ μ {S | ENNReal.ofReal (Real.exp ℓ) ≤ ENNReal.ofReal (Real.exp
      (∑ t : Fin k, w t (prefixSample S t t.isLt.le) (S t)))} := measure_mono hsub
    _ ≤ (∫⁻ S, ENNReal.ofReal (Real.exp
      (∑ t : Fin k, w t (prefixSample S t t.isLt.le) (S t))) ∂μ) / ENNReal.ofReal (Real.exp ℓ) := by
        apply meas_ge_le_lintegral_div hmeas.aemeasurable
        · simp [Real.exp_pos]
        · simp
    _ ≤ 1 / ENNReal.ofReal (Real.exp ℓ) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-ℓ)) := by
        rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]; simp

end OptimalAgnosticPAC.Dev.L33
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B
open OptimalAgnosticPAC.Learner
/-! Blueprint for Lemma 3.3 (q422). Stubs are proved in `L33PA.lean` (chain lemmas) and
`L33PB.lean` (core ERM bound and the final statement). -/
/-- The number of sample points lying in `C`, as a real number. -/
noncomputable def cnt {Z : Type} {k : ℕ} (C : Set Z) (S : Fin k → Z) : ℝ :=
  ((Finset.univ.filter (fun i => S i ∈ C)).card : ℝ)

end OptimalAgnosticPAC.Dev.L33B
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
lemma sqrt_le_of {x b : ℝ} (hb : 0 ≤ b) (h : x ≤ b ^ 2) : Real.sqrt x ≤ b := by
  calc Real.sqrt x ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

/-- Level 0 of the peeling. -/
lemma det0 {k ℓ L0 D c : ℝ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hL0 : 0 ≤ L0)
    (hc : c = Real.sqrt (L0 * ℓ / k))
    (hD : D ≤ 80 * (Real.sqrt (k * (2 ^ (0:ℕ) * (8 * L0 + 409600 * ℓ / k)) * (ℓ + ((0:ℕ):ℝ))) +
      (ℓ + ((0:ℕ):ℝ)))) :
    D ≤ k * (51280 * (c + ℓ / k)) := by
  have hk0 : (0:ℝ) < k := by linarith
  have hc0 : 0 ≤ c := hc ▸ Real.sqrt_nonneg _
  have hc2 : c ^ 2 = L0 * ℓ / k := by rw [hc, Real.sq_sqrt]; positivity
  have hkc : k ^ 2 * c ^ 2 = k * L0 * ℓ := by rw [hc2]; field_simp
  have hkL : 0 ≤ k * L0 * ℓ := by positivity
  have hs : Real.sqrt (k * (2 ^ (0:ℕ) * (8 * L0 + 409600 * ℓ / k)) * (ℓ + ((0:ℕ):ℝ))) ≤
      3 * (k * c) + 640 * ℓ := by
    apply sqrt_le_of (by positivity)
    have : k * (2 ^ (0:ℕ) * (8 * L0 + 409600 * ℓ / k)) * (ℓ + ((0:ℕ):ℝ)) =
        8 * (k * L0 * ℓ) + 409600 * ℓ ^ 2 := by
      field_simp; push_cast; ring
    rw [this]
    have hkc' : (k * c) ^ 2 = k * L0 * ℓ := by rw [mul_pow]; exact hkc
    nlinarith [mul_nonneg (mul_nonneg hk0.le hc0) (by linarith : (0:ℝ) ≤ ℓ)]
  have : k * (51280 * (c + ℓ / k)) = 51280 * (k * c) + 51280 * ℓ := by field_simp
  rw [this]
  push_cast at hD
  nlinarith [mul_nonneg hk0.le hc0]

/-- Level `j + 1` of the peeling: impossible. -/
lemma det1 {k ℓ L0 e : ℝ} (j : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hL0 : 0 ≤ L0)
    (he : 2 ^ j * (8 * L0 + 409600 * ℓ / k) - 2 * L0 < e)
    (hD : k * e ≤ 80 * (Real.sqrt (k * (2 ^ (j + 1) * (8 * L0 + 409600 * ℓ / k)) *
      (ℓ + ((j + 1 : ℕ) : ℝ))) + (ℓ + ((j + 1 : ℕ) : ℝ)))) : False := by
  have hk0 : (0:ℝ) < k := by linarith
  set s0 := 8 * L0 + 409600 * ℓ / k with hs0
  have hks0 : k * s0 = 8 * k * L0 + 409600 * ℓ := by rw [hs0]; field_simp
  have hpj : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hpow : ((j + 1 : ℕ) : ℝ) + 1 ≤ 2 ^ (j + 1) := by
    have := (j + 1).lt_two_pow_self
    exact_mod_cast this
  set ℓi := ℓ + ((j + 1 : ℕ) : ℝ) with hℓi
  set y := k * (2 ^ (j + 1) * s0) with hy
  have hy' : y = 2 ^ (j + 1) * (k * s0) := by rw [hy]; ring
  have hj0 : (0:ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by positivity
  have hyl : 409600 * ℓi ≤ y := by
    rw [hy', hks0, hℓi]
    have h1 : ((j + 1 : ℕ) : ℝ) * ℓ ≥ ((j + 1 : ℕ) : ℝ) := by nlinarith
    have h2 : 2 ^ (j + 1) * ℓ ≥ (((j + 1 : ℕ) : ℝ) + 1) * ℓ :=
      mul_le_mul_of_nonneg_right hpow (by linarith)
    have h3 : 0 ≤ 2 ^ (j + 1) * (8 * k * L0) := by positivity
    nlinarith
  have hy0 : 0 < y := by nlinarith
  have hsq : Real.sqrt (y * ℓi) ≤ y / 640 := by
    apply sqrt_le_of (by positivity)
    nlinarith
  have hD' : k * e ≤ 80 * (y / 640 + y / 409600) := by
    have : k * (2 ^ (j + 1) * s0) * ℓi = y * ℓi := by rw [hy]
    rw [this] at hD
    nlinarith
  have hs0' : 8 * L0 ≤ s0 := by
    rw [hs0]; have : 0 ≤ 409600 * ℓ / k := by positivity
    linarith
  have he' : 3 / 4 * (2 ^ j * s0) < e := by nlinarith
  have hy2 : y = 2 * k * (2 ^ j * s0) := by rw [hy, pow_succ]; ring
  nlinarith

lemma cnt_union {Z : Type} {k : ℕ} {A B : Set Z} (h : Disjoint A B) (S : Fin k → Z) :
    cnt (A ∪ B) S = cnt A S + cnt B S := by
  unfold cnt
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · congr 2; ext i; simp
  · exact Finset.disjoint_filter.2 (fun i _ h1 h2 => Set.disjoint_left.1 h h1 h2)

lemma err_cnt {X : Type} {k : ℕ} (h : X → Bool) (S : Fin k → X × Bool) :
    (errCount h S : ℝ) = cnt {z | h z.1 ≠ z.2} S := by
  unfold errCount cnt
  congr 2; ext i; simp

lemma bridge {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P] {k : ℕ}
    (hk : 1 ≤ k) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (S : Fin k → Z)
    (E F Xp Xm : Set Z) (hXp : MeasurableSet Xp) (hXm : MeasurableSet Xm)
    (hU : E ∪ Xm = F ∪ Xp) (h1 : Disjoint E Xm) (h2 : Disjoint F Xp) (hsub : Xm ⊆ F)
    (herm : cnt E S ≤ cnt F S)
    (hlow : ∀ i : ℕ, P.real Xp ≤ 2 ^ i * (8 * P.real F + 409600 * ℓ / k) →
      k * P.real Xp - cnt Xp S ≤
        40 * (Real.sqrt (k * (2 ^ i * (8 * P.real F + 409600 * ℓ / k)) * (ℓ + i)) + (ℓ + i)))
    (hup : ∀ i : ℕ, P.real Xm ≤ 2 ^ i * (8 * P.real F + 409600 * ℓ / k) →
      cnt Xm S - k * P.real Xm ≤
        40 * (Real.sqrt (k * (2 ^ i * (8 * P.real F + 409600 * ℓ / k)) * (ℓ + i)) + (ℓ + i))) :
    P.real E ≤ P.real F + 51280 * (Real.sqrt (P.real F * ℓ / k) + ℓ / k) := by
  have hR : P.real E + P.real Xm = P.real F + P.real Xp := by
    rw [← measureReal_union h1 hXm, hU, measureReal_union h2 hXp]
  have hC : cnt E S + cnt Xm S = cnt F S + cnt Xp S := by
    rw [← cnt_union h1, hU, cnt_union h2]
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hq0 : 0 ≤ P.real Xm := measureReal_nonneg
  have hp0 : 0 ≤ P.real Xp := measureReal_nonneg
  have hqL : P.real Xm ≤ P.real F := measureReal_mono hsub
  have hL0 : 0 ≤ P.real F := measureReal_nonneg
  set L0 := P.real F
  set s0 := 8 * L0 + 409600 * ℓ / k with hs0
  have hs0p : 0 < s0 := by rw [hs0]; positivity
  have hex : ∃ i : ℕ, P.real Xp + P.real Xm ≤ 2 ^ i * s0 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((P.real Xp + P.real Xm) / s0)
      (by norm_num : (1:ℝ) < 2)
    exact ⟨n, by rw [div_lt_iff₀ hs0p] at hn; linarith⟩
  obtain ⟨i, hi, hmin⟩ : ∃ i, P.real Xp + P.real Xm ≤ 2 ^ i * s0 ∧
      ∀ j < i, ¬ P.real Xp + P.real Xm ≤ 2 ^ j * s0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have key : k * (P.real E - L0) ≤
      80 * (Real.sqrt (k * (2 ^ i * s0) * (ℓ + i)) + (ℓ + i)) := by
    have a := hlow i (by linarith)
    have b := hup i (by linarith)
    have : k * (P.real E - L0) = (k * P.real Xp - cnt Xp S) + (cnt Xp S - cnt Xm S) +
        (cnt Xm S - k * P.real Xm) := by
      have : P.real E - L0 = P.real Xp - P.real Xm := by linarith
      rw [this]; ring
    rw [this]; linarith
  by_contra hcon
  rw [not_le] at hcon
  cases i with
  | zero =>
    have := det0 hk' hℓ hL0 rfl key
    have h2 : k * (51280 * (Real.sqrt (L0 * ℓ / k) + ℓ / k)) < k * (P.real E - L0) :=
      mul_lt_mul_of_pos_left (by linarith) hk0
    linarith
  | succ j =>
    have hj := hmin j (Nat.lt_succ_self j)
    exact det1 j hk' hℓ hL0 (e := P.real E - L0) (by rw [not_le] at hj; linarith) key

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
variable {X : Type}
/-- Lower-branch chain. -/
def Aset (p : X → ℝ) (u0 : ℝ) (b : Bool) (u : ℝ) : Set (X × Bool) :=
  {z | u ≤ p z.1 ∧ p z.1 < u0 ∧ z.2 = b}

/-- Upper-branch chain, indexed by `w = -u`. -/
def Bset (p : X → ℝ) (u0 : ℝ) (b : Bool) (w : ℝ) : Set (X × Bool) :=
  {z | u0 ≤ p z.1 ∧ p z.1 < -w ∧ z.2 = b}

lemma Aset_anti (p : X → ℝ) (u0 : ℝ) (b : Bool) : Antitone (Aset p u0 b) :=
  fun _ _ h _ hz => ⟨h.trans hz.1, hz.2⟩

lemma Bset_anti (p : X → ℝ) (u0 : ℝ) (b : Bool) : Antitone (Bset p u0 b) :=
  fun _ _ h _ hz => ⟨hz.1, hz.2.1.trans_le (neg_le_neg h), hz.2.2⟩

lemma Aset_meas [MeasurableSpace X] {p : X → ℝ} (hp : Measurable p) (u0 : ℝ) (b : Bool) (u : ℝ) :
    MeasurableSet (Aset p u0 b u) :=
  (measurableSet_le measurable_const (hp.comp measurable_fst)).inter
    ((measurableSet_lt (hp.comp measurable_fst) measurable_const).inter
      (measurable_snd (measurableSet_singleton b)))

lemma Bset_meas [MeasurableSpace X] {p : X → ℝ} (hp : Measurable p) (u0 : ℝ) (b : Bool) (w : ℝ) :
    MeasurableSet (Bset p u0 b w) :=
  (measurableSet_le measurable_const (hp.comp measurable_fst)).inter
    ((measurableSet_lt (hp.comp measurable_fst) measurable_const).inter
      (measurable_snd (measurableSet_singleton b)))

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
/-- Lower-deviation event of a chain (as in `chain_lower`). -/
def lowEv {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (k : ℕ) (s ℓ : ℝ) :
    Set (Fin k → Z) :=
  {S | ∃ u, P.real (A u) ≤ s ∧ 40 * (Real.sqrt (k * s * ℓ) + ℓ) < k * P.real (A u) - cnt (A u) S}

/-- Upper-deviation event of a chain (as in `chain_upper`). -/
def upEv {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (k : ℕ) (s ℓ : ℝ) :
    Set (Fin k → Z) :=
  {S | ∃ u, P.real (A u) ≤ s ∧ 40 * (Real.sqrt (k * s * ℓ) + ℓ) < cnt (A u) S - k * P.real (A u)}

/-- The four chain events at peeling level `i`. -/
def G {X : Type} [MeasurableSpace X] (P : Measure (X × Bool)) (p : X → ℝ) (u0 : ℝ) (k : ℕ)
    (s0 ℓ : ℝ) (i : ℕ) : Set (Fin k → X × Bool) :=
  lowEv P (Aset p u0 false) k (2 ^ i * s0) (ℓ + i) ∪ upEv P (Aset p u0 true) k (2 ^ i * s0) (ℓ + i) ∪
    lowEv P (Bset p u0 true) k (2 ^ i * s0) (ℓ + i) ∪ upEv P (Bset p u0 false) k (2 ^ i * s0) (ℓ + i)

lemma exp_split (ℓ : ℝ) (i : ℕ) : Real.exp (-(ℓ + i)) = Real.exp (-ℓ) * Real.exp (-1) ^ i := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartA
open OptimalAgnosticPAC.Learner
theorem cnt_eq_sum {Z : Type} {k : ℕ} (D : Set Z) (S : Fin k → Z) :
    cnt D S = ∑ i, D.indicator (1 : Z → ℝ) (S i) := by
  unfold cnt
  rw [Finset.natCast_card_filter]
  simp [Set.indicator_apply]

theorem cnt_mono {Z : Type} {k : ℕ} {C D : Set Z} (h : C ⊆ D) (S : Fin k → Z) :
    cnt C S ≤ cnt D S := by
  rw [cnt_eq_sum, cnt_eq_sum]
  exact Finset.sum_le_sum fun i _ =>
    Set.indicator_le_indicator_of_subset h (fun _ => by norm_num) _

theorem cnt_sdiff {Z : Type} {k : ℕ} {C D : Set Z} (h : C ⊆ D) (S : Fin k → Z) :
    cnt (D \ C) S = cnt D S - cnt C S := by
  rw [cnt_eq_sum, cnt_eq_sum, cnt_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.indicator_sdiff h]; rfl

/-- The Chernoff parameter. -/
noncomputable def lamOf (r ℓ' : ℝ) : ℝ := if 4 * ℓ' ≤ r then 2 * ℓ' / r else 1 / 2

theorem lamOf_spec (k σ ℓ' r T : ℝ) (hk : 0 ≤ k) (hℓ' : 0 < ℓ') (hr : 0 ≤ r)
    (hr2 : 3 * k * σ * ℓ' ≤ r ^ 2) (hT : r + 4 * ℓ' ≤ T) :
    0 < lamOf r ℓ' ∧ lamOf r ℓ' ≤ 1 / 2 ∧
      ℓ' ≤ lamOf r ℓ' * T - (3 * lamOf r ℓ' / 4) * lamOf r ℓ' * k * σ := by
  unfold lamOf
  split_ifs with h
  · have hr0 : 0 < r := by linarith
    refine ⟨by positivity, by rw [div_le_iff₀ hr0]; linarith, ?_⟩
    have e1 : 2 * ℓ' / r * T ≥ 2 * ℓ' / r * (r + 4 * ℓ') := by
      apply mul_le_mul_of_nonneg_left hT; positivity
    have e2 : 2 * ℓ' / r * (r + 4 * ℓ') = 2 * ℓ' + 8 * ℓ' ^ 2 / r := by
      field_simp; ring
    have e3 : (3 * (2 * ℓ' / r) / 4) * (2 * ℓ' / r) * k * σ = 3 * ℓ' ^ 2 * (k * σ) / r ^ 2 := by
      field_simp; ring
    have e4 : 3 * ℓ' ^ 2 * (k * σ) / r ^ 2 ≤ ℓ' := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e5 : 0 ≤ 8 * ℓ' ^ 2 / r := by positivity
    linarith
  · refine ⟨by norm_num, le_refl _, ?_⟩
    push Not at h
    -- k σ ≤ r^2/(3ℓ'), and r < 4ℓ'
    have e1 : 3 * (k * σ) * ℓ' ≤ r * (4 * ℓ') := by nlinarith
    have e2 : 3 * (k * σ) ≤ 4 * r := by
      by_contra hc; push Not at hc; nlinarith
    nlinarith

theorem sum_tail_up {Z : Type} {k : ℕ} (D : Set Z) (S : Fin k → Z) (p lam : ℝ) :
    ∑ i : Fin k, lam * (((0:ℝ) - p - (0 - D.indicator (1 : Z → ℝ) (S i))) -
        (3 * lam / 4) * (0 + p)) =
      lam * (cnt D S - k * p) - (3 * lam / 4) * lam * k * p := by
  have h : ∀ i, lam * (((0:ℝ) - p - (0 - D.indicator (1 : Z → ℝ) (S i))) -
      (3 * lam / 4) * (0 + p)) = lam * D.indicator (1 : Z → ℝ) (S i) -
        (lam * p + 3 * lam / 4 * lam * p) := fun i => by ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, cnt_eq_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_tail_lo {Z : Type} {k : ℕ} (D : Set Z) (S : Fin k → Z) (p lam : ℝ) :
    ∑ i : Fin k, lam * ((p - 0 - (D.indicator (1 : Z → ℝ) (S i) - 0)) -
        (3 * lam / 4) * (p + 0)) =
      lam * (k * p - cnt D S) - (3 * lam / 4) * lam * k * p := by
  have h : ∀ i, lam * ((p - 0 - (D.indicator (1 : Z → ℝ) (S i) - 0)) -
      (3 * lam / 4) * (p + 0)) = (lam * p - 3 * lam / 4 * lam * p) -
        lam * D.indicator (1 : Z → ℝ) (S i) := fun i => by ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, cnt_eq_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Fixed-set Bernstein bound, upper deviation. -/
theorem bern_up {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (k : ℕ) (D : Set Z) (hD : MeasurableSet D) (σ ℓ' r T : ℝ) (hℓ' : 0 < ℓ') (hr : 0 ≤ r)
    (hr2 : 3 * k * σ * ℓ' ≤ r ^ 2) (hT : r + 4 * ℓ' ≤ T) :
    Measure.pi (fun _ : Fin k => P)
      {S | P.real D ≤ σ ∧ T ≤ cnt D S - k * P.real D} ≤ ENNReal.ofReal (Real.exp (-ℓ')) := by
  obtain ⟨h0, h1, h2⟩ := lamOf_spec k σ ℓ' r T (by positivity) hℓ' hr hr2 hT
  refine le_trans (measure_mono ?_) (L33.tail P (fun _ => 0) (D.indicator 1) measurable_const
    (measurable_one.indicator hD) (fun _ => le_refl _) (fun _ => by norm_num)
    (fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun z => by by_cases h : z ∈ D <;> simp [h]) _ h0 h1 k ℓ')
  intro S ⟨hp, hS⟩
  simp only [Set.mem_ofPred_eq, integral_zero, integral_indicator_one hD]
  rw [sum_tail_up]
  have hp0 : 0 ≤ P.real D := measureReal_nonneg
  have : (3 * lamOf r ℓ' / 4) * lamOf r ℓ' * k * P.real D ≤
      (3 * lamOf r ℓ' / 4) * lamOf r ℓ' * k * σ := by
    apply mul_le_mul_of_nonneg_left hp; positivity
  have : lamOf r ℓ' * T ≤ lamOf r ℓ' * (cnt D S - k * P.real D) :=
    mul_le_mul_of_nonneg_left hS h0.le
  linarith

/-- Fixed-set Bernstein bound, lower deviation. -/
theorem bern_lo {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (k : ℕ) (D : Set Z) (hD : MeasurableSet D) (σ ℓ' r T : ℝ) (hℓ' : 0 < ℓ') (hr : 0 ≤ r)
    (hr2 : 3 * k * σ * ℓ' ≤ r ^ 2) (hT : r + 4 * ℓ' ≤ T) :
    Measure.pi (fun _ : Fin k => P)
      {S | P.real D ≤ σ ∧ T ≤ -(cnt D S - k * P.real D)} ≤
        ENNReal.ofReal (Real.exp (-ℓ')) := by
  obtain ⟨h0, h1, h2⟩ := lamOf_spec k σ ℓ' r T (by positivity) hℓ' hr hr2 hT
  refine le_trans (measure_mono ?_) (L33.tail P (D.indicator 1) (fun _ => 0)
    (measurable_one.indicator hD) measurable_const
    (fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun z => by by_cases h : z ∈ D <;> simp [h])
    (fun _ => le_refl _) (fun _ => by norm_num) _ h0 h1 k ℓ')
  intro S ⟨hp, hS⟩
  simp only [Set.mem_ofPred_eq, integral_zero, integral_indicator_one hD]
  rw [sum_tail_lo]
  have hp0 : 0 ≤ P.real D := measureReal_nonneg
  have : (3 * lamOf r ℓ' / 4) * lamOf r ℓ' * k * P.real D ≤
      (3 * lamOf r ℓ' / 4) * lamOf r ℓ' * k * σ := by
    apply mul_le_mul_of_nonneg_left hp; positivity
  have : lamOf r ℓ' * T ≤ lamOf r ℓ' * (-(cnt D S - k * P.real D)) :=
    mul_le_mul_of_nonneg_left hS h0.le
  linarith

theorem exists_countable_coinitial (U : Set ℝ) :
    ∃ V ⊆ U, V.Countable ∧ ∀ u ∈ U, ∃ v ∈ V, v ≤ u := by
  let g : {q : ℚ // ∃ u ∈ U, u ≤ (q : ℝ)} → ℝ := fun q => Classical.choose q.2
  have hg : ∀ q, g q ∈ U ∧ g q ≤ (q.1 : ℝ) := fun q => Classical.choose_spec q.2
  refine ⟨Set.range g ∪ {x | IsLeast U x}, ?_, ?_, ?_⟩
  · rintro x (⟨q, rfl⟩ | hx)
    · exact (hg q).1
    · exact hx.1
  · refine (Set.countable_range g).union ?_
    refine Set.Subsingleton.countable ?_
    intro x hx y hy
    exact hx.unique hy
  · intro u hu
    by_cases h : IsLeast U u
    · exact ⟨u, Or.inr h, le_refl _⟩
    · have : ∃ x ∈ U, x < u := by
        by_contra hc
        push Not at hc
        exact h ⟨hu, fun x hx => hc x hx⟩
      obtain ⟨x, hx, hxu⟩ := this
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxu
      let q' : {q : ℚ // ∃ u ∈ U, u ≤ (q : ℝ)} := ⟨q, x, hx, hq1.le⟩
      exact ⟨g q', Or.inl ⟨q', rfl⟩, ((hg q').2.trans hq2.le)⟩

theorem exists_countable_cofinal (U : Set ℝ) :
    ∃ V ⊆ U, V.Countable ∧ ∀ u ∈ U, ∃ v ∈ V, u ≤ v := by
  obtain ⟨V, hVU, hV, hcof⟩ := exists_countable_coinitial {x | -x ∈ U}
  refine ⟨(fun x => -x) '' V, ?_, hV.image _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hVU hx
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := hcof (-u) (by simpa using hu)
    exact ⟨-v, ⟨v, hv, rfl⟩, by linarith⟩

theorem real_biUnion_le {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (B : ℝ → Set Z) (V : Set ℝ) (hV : V.Countable) (hd : DirectedOn (Function.onFun (fun x y : Set Z => x ⊆ y) B) V)
    (a : ℝ) (ha : 0 ≤ a) (h : ∀ v ∈ V, P.real (B v) ≤ a) :
    P.real (⋃ v ∈ V, B v) ≤ a := by
  apply ENNReal.toReal_le_of_le_ofReal ha
  rw [measure_biUnion_eq_iSup hV hd]
  refine iSup₂_le fun v hv => ?_
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (h v hv)

/-- Closure from above: union of all chain members of mass at most `a`. -/
def Gup {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (a : ℝ) : Set Z :=
  ⋃ u ∈ {u | P.real (A u) ≤ a}, A u

/-- Closure from below: intersection of all chain members of mass at least `b`. -/
def Glo {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (b : ℝ) : Set Z :=
  ⋂ u ∈ {u | b ≤ P.real (A u)}, A u

theorem Gup_eq {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (hA : Antitone A)
    (a : ℝ) : ∃ V ⊆ {u | P.real (A u) ≤ a}, V.Countable ∧ Gup P A a = ⋃ v ∈ V, A v := by
  obtain ⟨V, hVU, hV, hcof⟩ := exists_countable_coinitial {u | P.real (A u) ≤ a}
  refine ⟨V, hVU, hV, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    simp only [Gup, Set.mem_iUnion] at hz ⊢
    obtain ⟨u, hu, hz⟩ := hz
    obtain ⟨v, hv, hvu⟩ := hcof u hu
    exact ⟨v, hv, hA hvu hz⟩
  · exact Set.biUnion_subset_biUnion_left hVU

theorem Glo_eq {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (hA : Antitone A)
    (b : ℝ) : ∃ V ⊆ {u | b ≤ P.real (A u)}, V.Countable ∧ Glo P A b = ⋂ v ∈ V, A v := by
  obtain ⟨V, hVU, hV, hcof⟩ := exists_countable_cofinal {u | b ≤ P.real (A u)}
  refine ⟨V, hVU, hV, ?_⟩
  apply Set.Subset.antisymm
  · exact Set.biInter_subset_biInter_left hVU
  · intro z hz
    simp only [Glo, Set.mem_iInter] at hz ⊢
    intro u hu
    obtain ⟨v, hv, huv⟩ := hcof u hu
    exact hA huv (hz v hv)

theorem measurable_Gup {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z)
    (hA : Antitone A) (hAm : ∀ u, MeasurableSet (A u)) (a : ℝ) : MeasurableSet (Gup P A a) := by
  obtain ⟨V, -, hV, he⟩ := Gup_eq P A hA a
  rw [he]; exact MeasurableSet.biUnion hV fun v _ => hAm v

theorem measurable_Glo {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z)
    (hA : Antitone A) (hAm : ∀ u, MeasurableSet (A u)) (b : ℝ) : MeasurableSet (Glo P A b) := by
  obtain ⟨V, -, hV, he⟩ := Glo_eq P A hA b
  rw [he]; exact MeasurableSet.biInter hV fun v _ => hAm v

theorem Gup_real_le {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (A : ℝ → Set Z) (hA : Antitone A) (a : ℝ) (ha : 0 ≤ a) : P.real (Gup P A a) ≤ a := by
  obtain ⟨V, hVU, hV, he⟩ := Gup_eq P A hA a
  rw [he]
  refine real_biUnion_le P A V hV ?_ a ha fun v hv => hVU hv
  intro x hx y hy
  rcases le_total x y with h | h
  · exact ⟨x, hx, le_refl _, hA h⟩
  · exact ⟨y, hy, hA h, le_refl _⟩

theorem le_Glo_real {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (A : ℝ → Set Z) (hA : Antitone A) (hAm : ∀ u, MeasurableSet (A u)) (b : ℝ) (hb : b ≤ 1) :
    b ≤ P.real (Glo P A b) := by
  obtain ⟨V, hVU, hV, he⟩ := Glo_eq P A hA b
  have hc : (Glo P A b)ᶜ = ⋃ v ∈ V, (A v)ᶜ := by rw [he]; simp [Set.compl_iInter]
  have hm := measurable_Glo P A hA hAm b
  have h1 : P.real (Glo P A b)ᶜ ≤ 1 - b := by
    rw [hc]
    refine real_biUnion_le P (fun v => (A v)ᶜ) V hV ?_ (1 - b) (by linarith) fun v hv => ?_
    · intro x hx y hy
      rcases le_total x y with h | h
      · exact ⟨y, hy, Set.compl_subset_compl.mpr (hA h), le_refl _⟩
      · exact ⟨x, hx, le_refl _, Set.compl_subset_compl.mpr (hA h)⟩
    · rw [measureReal_compl (hAm v), probReal_univ]
      have := hVU hv; simp only [Set.mem_ofPred_eq] at this; linarith
  rw [measureReal_compl hm, probReal_univ] at h1
  linarith

theorem subset_Gup {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (u a : ℝ)
    (h : P.real (A u) ≤ a) : A u ⊆ Gup P A a :=
  Set.subset_biUnion_of_mem (u := A) (show u ∈ {u | P.real (A u) ≤ a} from h)

theorem Glo_subset {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) (u b : ℝ)
    (h : b ≤ P.real (A u)) : Glo P A b ⊆ A u :=
  Set.biInter_subset_of_mem (show u ∈ {u | b ≤ P.real (A u)} from h)

theorem Gup_mono {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) {a a' : ℝ}
    (h : a ≤ a') : Gup P A a ⊆ Gup P A a' :=
  Set.biUnion_subset_biUnion_left fun _ hu => le_trans hu h

theorem Glo_mono {Z : Type} [MeasurableSpace Z] (P : Measure Z) (A : ℝ → Set Z) {b b' : ℝ}
    (h : b ≤ b') : Glo P A b ⊆ Glo P A b' :=
  Set.biInter_subset_biInter_left fun _ hu => le_trans h hu

end OptimalAgnosticPAC.Dev.L33B.PartA
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartA
theorem geom_sum1 (M : ℕ) :
    ∑ m ∈ Finset.range M, ((m : ℝ) + 2) * (1 / 2) ^ m + (2 * (M : ℝ) + 6) * (1 / 2) ^ M = 6 := by
  induction M with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    push_cast
    linarith

theorem nat_sq_le (M : ℕ) : 4 * (M + 1) ^ 2 ≤ 9 * 2 ^ M := by
  induction M with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num
    · have e : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [e]; nlinarith

theorem sum_lin (M : ℕ) (ℓ : ℝ) :
    ∑ m ∈ Finset.range M, 4 * (ℓ + 2 * ((m : ℝ) + 1)) = 4 * M * ℓ + 4 * M * (M + 1) := by
  induction M with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem geom_sum2 (M : ℕ) :
    ∑ m ∈ Finset.range M, ((4 : ℝ) / 7) ^ (m + 1) = 4 / 3 * (1 - (4 / 7) ^ M) := by
  induction M with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem exp_neg_two_le : Real.exp (-2) ≤ 1 / 7 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [Real.exp_neg, h2]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  nlinarith

theorem sum_fail (M : ℕ) (ℓ : ℝ) :
    2 * Real.exp (-ℓ) + ∑ m ∈ Finset.range M,
      ((4 : ℝ) ^ (m + 1) + 1) * Real.exp (-(ℓ + 2 * ((m : ℝ) + 1))) ≤ 5 * Real.exp (-ℓ) := by
  have he := exp_neg_two_le
  have he0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  have hterm : ∀ m : ℕ, ((4 : ℝ) ^ (m + 1) + 1) * Real.exp (-(ℓ + 2 * ((m : ℝ) + 1))) ≤
      2 * Real.exp (-ℓ) * ((4 : ℝ) / 7) ^ (m + 1) := by
    intro m
    have h1 : Real.exp (-(ℓ + 2 * ((m : ℝ) + 1))) = Real.exp (-ℓ) * Real.exp (-2) ^ (m + 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    have h2 : Real.exp (-2) ^ (m + 1) ≤ (1 / 7) ^ (m + 1) := pow_le_pow_left₀ he0 he _
    have h3 : (1 : ℝ) ≤ 4 ^ (m + 1) := one_le_pow₀ (by norm_num)
    have h4 : ((4 : ℝ) / 7) ^ (m + 1) = 4 ^ (m + 1) * (1 / 7) ^ (m + 1) := by
      rw [← mul_pow]; norm_num
    rw [h1, h4]
    have hl : 0 < Real.exp (-ℓ) := Real.exp_pos _
    have h5 : 0 ≤ Real.exp (-2) ^ (m + 1) := pow_nonneg he0 _
    have : ((4 : ℝ) ^ (m + 1) + 1) * Real.exp (-2) ^ (m + 1) ≤
        2 * (4 ^ (m + 1) * (1 / 7) ^ (m + 1)) := by nlinarith
    nlinarith
  have hs := Finset.sum_le_sum fun m (_ : m ∈ Finset.range M) => hterm m
  rw [← Finset.mul_sum, geom_sum2] at hs
  have : (0 : ℝ) ≤ (4 / 7) ^ M := by positivity
  have hl : 0 < Real.exp (-ℓ) := Real.exp_pos _
  nlinarith

theorem main_arith (k s ℓ X : ℝ) (M : ℕ) (hk : 0 ≤ k) (hs : 0 ≤ s) (hℓ : 1 ≤ ℓ)
    (hX : X = Real.sqrt (k * s * ℓ)) (hM1 : k * s ≤ ℓ * 4 ^ M)
    (hM2 : M = 0 ∨ ℓ * 4 ^ (M - 1) < k * s) :
    (7 / 4 * X + 4 * ℓ) + ∑ m ∈ Finset.range M,
      (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m + 4 * (ℓ + 2 * ((m : ℝ) + 1))) +
      k * s / 4 ^ M ≤ 40 * (X + ℓ) := by
  have hX0 : 0 ≤ X := hX ▸ Real.sqrt_nonneg _
  have hS1 : ∑ m ∈ Finset.range M, ((m : ℝ) + 2) * (1 / 2) ^ m ≤ 6 := by
    have := geom_sum1 M
    have : 0 ≤ (2 * (M : ℝ) + 6) * (1 / 2) ^ M := by positivity
    linarith
  rw [Finset.sum_add_distrib, sum_lin]
  have he : ∑ m ∈ Finset.range M, 7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m =
      7 / 4 * X * ∑ m ∈ Finset.range M, ((m : ℝ) + 2) * (1 / 2) ^ m := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
  rw [he]
  have h2 : ℓ * 2 ^ M ≤ ℓ + 2 * X := by
    rcases hM2 with h | h
    · subst h; simp; linarith
    · cases M with
      | zero => simp; linarith
      | succ n =>
      simp only [Nat.add_sub_cancel] at h
      have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have : ℓ * 2 ^ n ≤ X := by
        rw [hX]
        apply Real.le_sqrt_of_sq_le
        rw [h4] at h
        nlinarith
      rw [pow_succ]; linarith
  have h3 : 4 * (M : ℝ) * ℓ + 4 * M * (M + 1) ≤ 9 * ℓ * 2 ^ M := by
    have := nat_sq_le M
    have hc : 4 * ((M : ℝ) + 1) ^ 2 ≤ 9 * 2 ^ M := by exact_mod_cast this
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have a : 4 * (M : ℝ) * (M + 1) ≤ 4 * M * (M + 1) * ℓ := by
      have : 0 ≤ 4 * (M : ℝ) * (M + 1) := by positivity
      nlinarith
    have b : ℓ * (4 * ((M : ℝ) + 1) ^ 2) ≤ ℓ * (9 * 2 ^ M) :=
      mul_le_mul_of_nonneg_left hc (by linarith)
    nlinarith
  have h4 : k * s / 4 ^ M ≤ ℓ := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h5 : 7 / 4 * X * ∑ m ∈ Finset.range M, ((m : ℝ) + 2) * (1 / 2) ^ m ≤ 7 / 4 * X * 6 :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  nlinarith

end OptimalAgnosticPAC.Dev.L33B.PartA
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartA
theorem union_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E0 : ℕ → Set Ω)
    (E : ℕ → ℕ → Set Ω) (M : ℕ) (ℓ : ℝ)
    (h0 : ∀ j, μ (E0 j) ≤ ENNReal.ofReal (Real.exp (-ℓ)))
    (h : ∀ m j, μ (E m j) ≤ ENNReal.ofReal (Real.exp (-(ℓ + 2 * ((m : ℝ) + 1))))) :
    μ ((⋃ j ∈ Finset.range 2, E0 j) ∪
        ⋃ m ∈ Finset.range M, ⋃ j ∈ Finset.range (4 ^ (m + 1) + 1), E m j) ≤
      ENNReal.ofReal (5 * Real.exp (-ℓ)) := by
  have a : μ (⋃ j ∈ Finset.range 2, E0 j) ≤ ENNReal.ofReal (2 * Real.exp (-ℓ)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => h0 j).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    simp
  have b : μ (⋃ m ∈ Finset.range M, ⋃ j ∈ Finset.range (4 ^ (m + 1) + 1), E m j) ≤
      ENNReal.ofReal (∑ m ∈ Finset.range M,
        ((4 : ℝ) ^ (m + 1) + 1) * Real.exp (-(ℓ + 2 * ((m : ℝ) + 1)))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_le_sum fun m _ => ?_
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => h m j).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    simp
  refine (measure_union_le _ _).trans ((add_le_add a b).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (sum_fail M ℓ)

theorem exists_M (k s ℓ : ℝ) (hℓ : 1 ≤ ℓ) :
    ∃ M : ℕ, k * s ≤ ℓ * 4 ^ M ∧ (M = 0 ∨ ℓ * 4 ^ (M - 1) < k * s) := by
  have hex : ∃ M : ℕ, k * s ≤ ℓ * 4 ^ M := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (k * s) (by norm_num : (1 : ℝ) < 4)
    refine ⟨n, ?_⟩
    have : (0 : ℝ) < 4 ^ n := by positivity
    nlinarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · exact Or.inl h
  · right
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    exact this

theorem ceil_parent (y : ℝ) (hy : 0 ≤ y) : ⌈y⌉₊ = (⌈4 * y⌉₊ + 3) / 4 := by
  have h1 : ⌈4 * y⌉₊ ≤ 4 * ⌈y⌉₊ := Nat.ceil_le.2 (by push_cast; linarith [Nat.le_ceil y])
  have h2 : 4 * ⌈y⌉₊ < ⌈4 * y⌉₊ + 4 := by
    have a := Nat.ceil_lt_add_one hy
    have b := Nat.le_ceil (4 * y)
    have : ((4 * ⌈y⌉₊ : ℕ) : ℝ) < ((⌈4 * y⌉₊ + 4 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

theorem floor_parent (y : ℝ) (hy : 0 ≤ y) : ⌊y⌋₊ = ⌊4 * y⌋₊ / 4 := by
  have h1 : 4 * ⌊y⌋₊ ≤ ⌊4 * y⌋₊ := Nat.le_floor (by push_cast; linarith [Nat.floor_le hy])
  have h2 : ⌊4 * y⌋₊ < 4 * ⌊y⌋₊ + 4 :=
    (Nat.floor_lt (by linarith)).2 (by push_cast; linarith [Nat.lt_floor_add_one y])
  omega

theorem r_ok (k s ℓ X : ℝ) (m : ℕ) (hk : 0 ≤ k) (hs : 0 ≤ s) (hℓ : 1 ≤ ℓ)
    (hX : X = Real.sqrt (k * s * ℓ)) :
    3 * k * (s / 4 ^ m) * (ℓ + 2 * ((m : ℝ) + 1)) ≤ (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m) ^ 2 := by
  have hX2 : X ^ 2 = k * s * ℓ := by rw [hX, Real.sq_sqrt (by positivity)]
  have hq : ((1 : ℝ) / 2) ^ m * (1 / 2) ^ m = 1 / 4 ^ m := by
    rw [← mul_pow, div_mul_div_comm, one_mul, div_pow, one_pow]; norm_num
  have e : (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m) ^ 2 =
      49 / 16 * ((m : ℝ) + 2) ^ 2 * (k * s * ℓ) * (1 / 4 ^ m) := by
    rw [← hq, ← hX2]; ring
  rw [e]
  have e2 : 3 * k * (s / 4 ^ m) * (ℓ + 2 * ((m : ℝ) + 1)) =
      3 * (ℓ + 2 * ((m : ℝ) + 1)) * (k * s) * (1 / 4 ^ m) := by ring
  rw [e2]
  have hks : 0 ≤ k * s * (1 / 4 ^ m) := by positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have key : 3 * (ℓ + 2 * ((m : ℝ) + 1)) ≤ 49 / 16 * ((m : ℝ) + 2) ^ 2 * ℓ := by
    have h1 : ((m : ℝ) ^ 2 + 4 * m + 3) * 1 ≤ ((m : ℝ) ^ 2 + 4 * m + 3) * ℓ :=
      mul_le_mul_of_nonneg_left hℓ (by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_right key hks
  nlinarith

theorem r0_ok (k s ℓ X : ℝ) (hk : 0 ≤ k) (hs : 0 ≤ s) (hℓ : 1 ≤ ℓ)
    (hX : X = Real.sqrt (k * s * ℓ)) : 3 * k * s * ℓ ≤ (7 / 4 * X) ^ 2 := by
  have hX2 : X ^ 2 = k * s * ℓ := by rw [hX, Real.sq_sqrt (by positivity)]
  have : 0 ≤ k * s * ℓ := by positivity
  nlinarith

theorem path_total (d : ℕ → ℝ) (M : ℕ) (T0 : ℝ) (T : ℕ → ℝ) (h0 : d 0 < T0)
    (h : ∀ m < M, d (m + 1) - d m < T m) :
    d M < T0 + ∑ m ∈ Finset.range M, T m := by
  have hs := Finset.sum_range_sub d M
  have : ∑ m ∈ Finset.range M, (d (m + 1) - d m) ≤ ∑ m ∈ Finset.range M, T m :=
    Finset.sum_le_sum fun m hm => (h m (Finset.mem_range.1 hm)).le
  linarith

end OptimalAgnosticPAC.Dev.L33B.PartA
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartA
open OptimalAgnosticPAC.Learner
/-! Proofs of the Blueprint's chain lemmas `chain_upper` and `chain_lower` (q422). -/
/-- Uniform upper deviation over a chain of sets (antitone family), restricted to members of mass
at most `s`; no `log k` factor. Proved by chaining over a base-4 mass grid. -/
theorem chain_upper {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (A : ℝ → Set Z) (hA : Antitone A) (hAm : ∀ u, MeasurableSet (A u))
    (k : ℕ) (s ℓ : ℝ) (hs : 0 < s) (hℓ : 1 ≤ ℓ) :
    Measure.pi (fun _ : Fin k => P)
      {S | ∃ u, P.real (A u) ≤ s ∧
        40 * (Real.sqrt (k * s * ℓ) + ℓ) < cnt (A u) S - k * P.real (A u)} ≤
      ENNReal.ofReal (5 * Real.exp (-ℓ)) := by
  set μ := Measure.pi (fun _ : Fin k => P) with hμ
  obtain ⟨M, hM1, hM2⟩ := exists_M (k : ℝ) s ℓ hℓ
  set X := Real.sqrt (k * s * ℓ) with hX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hℓ0 : 0 < ℓ := by linarith
  set G := Gup P A with hG
  have hGm : ∀ a, MeasurableSet (G a) := measurable_Gup P A hA hAm
  set T : ℕ → ℝ := fun m =>
    7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m + 4 * (ℓ + 2 * ((m : ℝ) + 1)) with hT
  set E0 : ℕ → Set (Fin k → Z) := fun j =>
    {S | P.real (G ((j : ℝ) * s / 4 ^ 0)) ≤ s ∧ 7 / 4 * X + 4 * ℓ ≤
      cnt (G ((j : ℝ) * s / 4 ^ 0)) S - k * P.real (G ((j : ℝ) * s / 4 ^ 0))} with hE0
  set D : ℕ → ℕ → Set Z := fun m j =>
    G ((((j + 3) / 4 : ℕ) : ℝ) * s / 4 ^ m) \ G ((j : ℝ) * s / 4 ^ (m + 1)) with hD
  set E : ℕ → ℕ → Set (Fin k → Z) := fun m j =>
    {S | P.real (D m j) ≤ s / 4 ^ m ∧ T m ≤ -(cnt (D m j) S - k * P.real (D m j))} with hE
  have h0 : ∀ j, μ (E0 j) ≤ ENNReal.ofReal (Real.exp (-ℓ)) := fun j =>
    bern_up P k _ (hGm _) s ℓ (7 / 4 * X) _ hℓ0 (by positivity)
      (r0_ok _ _ _ _ hk0 hs.le hℓ hX) le_rfl
  have h1 : ∀ m j, μ (E m j) ≤ ENNReal.ofReal (Real.exp (-(ℓ + 2 * ((m : ℝ) + 1)))) :=
    fun m j => bern_lo P k _ ((hGm _).diff (hGm _)) (s / 4 ^ m) (ℓ + 2 * ((m : ℝ) + 1))
      (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m) _
      (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) (by positivity)
      (r_ok _ _ _ _ m hk0 hs.le hℓ hX) le_rfl
  refine le_trans (measure_mono ?_) (union_bound μ E0 E M ℓ h0 h1)
  rintro S ⟨u, hu, hbad⟩
  by_contra hn
  set c := P.real (A u) with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hy : ∀ m : ℕ, 0 ≤ c * 4 ^ m / s := fun m => by positivity
  set j : ℕ → ℕ := fun m => ⌈c * 4 ^ m / s⌉₊ with hjdef
  set a : ℕ → ℝ := fun m => (j m : ℝ) * s / 4 ^ m with hadef
  have ha1 : ∀ m, c ≤ a m := fun m => by
    have := Nat.le_ceil (c * 4 ^ m / s)
    show c ≤ (⌈c * 4 ^ m / s⌉₊ : ℝ) * s / 4 ^ m
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hs] at this; linarith
  have ha2 : ∀ m, a m ≤ c + s / 4 ^ m := fun m => by
    have h := Nat.ceil_lt_add_one (hy m)
    show (⌈c * 4 ^ m / s⌉₊ : ℝ) * s / 4 ^ m ≤ c + s / 4 ^ m
    have h4 : (0 : ℝ) < 4 ^ m := by positivity
    rw [div_le_iff₀ h4, add_mul, div_mul_cancel₀ _ h4.ne']
    have h' : (⌈c * 4 ^ m / s⌉₊ : ℝ) * s < (c * 4 ^ m / s + 1) * s :=
      mul_lt_mul_of_pos_right h hs
    rw [add_mul, div_mul_cancel₀ _ hs.ne'] at h'; linarith
  have hj : ∀ m, j m = (j (m + 1) + 3) / 4 := fun m => by
    show ⌈c * 4 ^ m / s⌉₊ = (⌈c * 4 ^ (m + 1) / s⌉₊ + 3) / 4
    rw [show c * 4 ^ (m + 1) / s = 4 * (c * 4 ^ m / s) by ring]
    exact ceil_parent _ (hy m)
  have hjle : ∀ m, j m ≤ 4 ^ m := fun m => Nat.ceil_le.2 (by
    push_cast; rw [div_le_iff₀ hs]
    have : (0 : ℝ) < 4 ^ m := by positivity
    nlinarith)
  have hamono : ∀ m, a (m + 1) ≤ a m := fun m => by
    have h := hj m
    have h' : j (m + 1) ≤ 4 * j m := by omega
    have hc' : (j (m + 1) : ℝ) ≤ 4 * j m := by exact_mod_cast h'
    show (j (m + 1) : ℝ) * s / 4 ^ (m + 1) ≤ (j m : ℝ) * s / 4 ^ m
    rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ s * 4 ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hc' this]
  set g : ℕ → Set Z := fun m => G (a m) with hgdef
  set d : ℕ → ℝ := fun m => cnt (g m) S - k * P.real (g m) with hddef
  have hsub : ∀ m, A u ⊆ g m := fun m => subset_Gup P A u (a m) (ha1 m)
  have hPg1 : ∀ m, c ≤ P.real (g m) := fun m => measureReal_mono (hsub m)
  have hPg2 : ∀ m, P.real (g m) ≤ a m := fun m => Gup_real_le P A hA (a m) (hc0.trans (ha1 m))
  have hgg : ∀ m, g (m + 1) ⊆ g m := fun m => Gup_mono P A (hamono m)
  have hd0 : d 0 < 7 / 4 * X + 4 * ℓ := by
    by_contra h
    push Not at h
    have hj0 : (j 0 : ℝ) ≤ 1 := by exact_mod_cast hjle 0
    apply hn
    refine Or.inl (Set.mem_iUnion₂.2 ⟨j 0, Finset.mem_range.2 (by have := hjle 0; simp at this; omega), ?_⟩)
    refine ⟨?_, h⟩
    have := hPg2 0
    show P.real (g 0) ≤ s
    have : a 0 ≤ s := by
      show (j 0 : ℝ) * s / 4 ^ 0 ≤ s
      rw [pow_zero, div_one]; nlinarith
    linarith
  have hstep : ∀ m < M, d (m + 1) - d m < T m := by
    intro m hm
    by_contra h
    push Not at h
    apply hn
    refine Or.inr (Set.mem_iUnion₂.2 ⟨m, Finset.mem_range.2 hm, Set.mem_iUnion₂.2
      ⟨j (m + 1), Finset.mem_range.2 (by have := hjle (m + 1); omega), ?_⟩⟩)
    have hDe : D m (j (m + 1)) = g m \ g (m + 1) := by
      show G ((((j (m + 1) + 3) / 4 : ℕ) : ℝ) * s / 4 ^ m) \ G ((j (m + 1) : ℝ) * s / 4 ^ (m + 1)) =
        G (a m) \ G (a (m + 1))
      rw [← hj m]
    show P.real (D m (j (m + 1))) ≤ s / 4 ^ m ∧
      T m ≤ -(cnt (D m (j (m + 1))) S - k * P.real (D m (j (m + 1))))
    rw [hDe, cnt_sdiff (hgg m), measureReal_sdiff (hgg m) (hGm _)]
    refine ⟨by linarith [hPg2 m, hPg1 (m + 1), ha2 m], ?_⟩
    have e : d (m + 1) - d m = -(cnt (g m) S - cnt (g (m + 1)) S -
        k * (P.real (g m) - P.real (g (m + 1)))) := by
      simp only [hddef]; ring
    linarith
  have hfin : cnt (A u) S - k * c ≤ d M + k * s / 4 ^ M := by
    have h1 := cnt_mono (hsub M) S
    have h2 : k * (P.real (g M) - c) ≤ k * (s / 4 ^ M) :=
      mul_le_mul_of_nonneg_left (by linarith [hPg2 M, ha2 M]) hk0
    have e : d M = cnt (g M) S - k * P.real (g M) := rfl
    rw [mul_div_assoc]
    linarith
  have hp := path_total d M _ T hd0 hstep
  have hm := main_arith k s ℓ X M hk0 hs.le hℓ hX hM1 hM2
  have hTe : ∑ m ∈ Finset.range M, T m = ∑ m ∈ Finset.range M,
      (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m + 4 * (ℓ + 2 * ((m : ℝ) + 1))) := rfl
  linarith

end OptimalAgnosticPAC.Dev.L33B.PartA
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B
open OptimalAgnosticPAC.Learner
alias chain_upper := OptimalAgnosticPAC.Dev.L33B.PartA.chain_upper

end OptimalAgnosticPAC.Dev.L33B
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartA
open OptimalAgnosticPAC.Learner
/-- Uniform lower deviation over a chain of sets, restricted to members of mass at most `s`. -/
theorem chain_lower {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (A : ℝ → Set Z) (hA : Antitone A) (hAm : ∀ u, MeasurableSet (A u))
    (k : ℕ) (s ℓ : ℝ) (hs : 0 < s) (hℓ : 1 ≤ ℓ) :
    Measure.pi (fun _ : Fin k => P)
      {S | ∃ u, P.real (A u) ≤ s ∧
        40 * (Real.sqrt (k * s * ℓ) + ℓ) < k * P.real (A u) - cnt (A u) S} ≤
      ENNReal.ofReal (5 * Real.exp (-ℓ)) := by
  set μ := Measure.pi (fun _ : Fin k => P) with hμ
  obtain ⟨M, hM1, hM2⟩ := exists_M (k : ℝ) s ℓ hℓ
  set X := Real.sqrt (k * s * ℓ) with hX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hℓ0 : 0 < ℓ := by linarith
  set G := Glo P A with hG
  have hGm : ∀ a, MeasurableSet (G a) := measurable_Glo P A hA hAm
  set T : ℕ → ℝ := fun m =>
    7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m + 4 * (ℓ + 2 * ((m : ℝ) + 1)) with hT
  set E0 : ℕ → Set (Fin k → Z) := fun j =>
    {S | P.real (G ((j : ℝ) * s / 4 ^ 0)) ≤ s ∧ 7 / 4 * X + 4 * ℓ ≤
      -(cnt (G ((j : ℝ) * s / 4 ^ 0)) S - k * P.real (G ((j : ℝ) * s / 4 ^ 0)))} with hE0
  set D : ℕ → ℕ → Set Z := fun m j =>
    G ((j : ℝ) * s / 4 ^ (m + 1)) \ G (((j / 4 : ℕ) : ℝ) * s / 4 ^ m) with hD
  set E : ℕ → ℕ → Set (Fin k → Z) := fun m j =>
    {S | P.real (D m j) ≤ s / 4 ^ m ∧ T m ≤ -(cnt (D m j) S - k * P.real (D m j))} with hE
  have h0 : ∀ j, μ (E0 j) ≤ ENNReal.ofReal (Real.exp (-ℓ)) := fun j =>
    bern_lo P k _ (hGm _) s ℓ (7 / 4 * X) _ hℓ0 (by positivity)
      (r0_ok _ _ _ _ hk0 hs.le hℓ hX) le_rfl
  have h1 : ∀ m j, μ (E m j) ≤ ENNReal.ofReal (Real.exp (-(ℓ + 2 * ((m : ℝ) + 1)))) :=
    fun m j => bern_lo P k _ ((hGm _).diff (hGm _)) (s / 4 ^ m) (ℓ + 2 * ((m : ℝ) + 1))
      (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m) _
      (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) (by positivity)
      (r_ok _ _ _ _ m hk0 hs.le hℓ hX) le_rfl
  refine le_trans (measure_mono ?_) (union_bound μ E0 E M ℓ h0 h1)
  rintro S ⟨u, hu, hbad⟩
  by_contra hn
  set c := P.real (A u) with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c ≤ 1 := measureReal_le_one
  have hy : ∀ m : ℕ, 0 ≤ c * 4 ^ m / s := fun m => by positivity
  set j : ℕ → ℕ := fun m => ⌊c * 4 ^ m / s⌋₊ with hjdef
  set b : ℕ → ℝ := fun m => (j m : ℝ) * s / 4 ^ m with hbdef
  have hb0 : ∀ m, 0 ≤ b m := fun m => by positivity
  have hb1 : ∀ m, b m ≤ c := fun m => by
    have := Nat.floor_le (hy m)
    show (⌊c * 4 ^ m / s⌋₊ : ℝ) * s / 4 ^ m ≤ c
    rw [div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ hs] at this; linarith
  have hb2 : ∀ m, c ≤ b m + s / 4 ^ m := fun m => by
    have h := Nat.lt_floor_add_one (c * 4 ^ m / s)
    show c ≤ (⌊c * 4 ^ m / s⌋₊ : ℝ) * s / 4 ^ m + s / 4 ^ m
    have h4 : (0 : ℝ) < 4 ^ m := by positivity
    rw [← add_div, le_div_iff₀ h4]
    have h' : (c * 4 ^ m / s) * s < (⌊c * 4 ^ m / s⌋₊ + 1) * s :=
      mul_lt_mul_of_pos_right h hs
    rw [div_mul_cancel₀ _ hs.ne'] at h'; linarith
  have hj : ∀ m, j m = j (m + 1) / 4 := fun m => by
    show ⌊c * 4 ^ m / s⌋₊ = ⌊c * 4 ^ (m + 1) / s⌋₊ / 4
    rw [show c * 4 ^ (m + 1) / s = 4 * (c * 4 ^ m / s) by ring]
    exact floor_parent _ (hy m)
  have hjle : ∀ m, j m ≤ 4 ^ m := fun m => Nat.floor_le_of_le (by
    push_cast; rw [div_le_iff₀ hs]
    have : (0 : ℝ) < 4 ^ m := by positivity
    nlinarith)
  have hbmono : ∀ m, b m ≤ b (m + 1) := fun m => by
    have h := hj m
    have h' : 4 * j m ≤ j (m + 1) := by omega
    have hc' : 4 * (j m : ℝ) ≤ j (m + 1) := by exact_mod_cast h'
    show (j m : ℝ) * s / 4 ^ m ≤ (j (m + 1) : ℝ) * s / 4 ^ (m + 1)
    rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ s * 4 ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hc' this]
  set g : ℕ → Set Z := fun m => G (b m) with hgdef
  set d : ℕ → ℝ := fun m => -(cnt (g m) S - k * P.real (g m)) with hddef
  have hsub : ∀ m, g m ⊆ A u := fun m => Glo_subset P A u (b m) (hb1 m)
  have hPg1 : ∀ m, P.real (g m) ≤ c := fun m => measureReal_mono (hsub m)
  have hPg2 : ∀ m, b m ≤ P.real (g m) := fun m =>
    le_Glo_real P A hA hAm (b m) ((hb1 m).trans hc1)
  have hgg : ∀ m, g m ⊆ g (m + 1) := fun m => Glo_mono P A (hbmono m)
  have hd0 : d 0 < 7 / 4 * X + 4 * ℓ := by
    by_contra h
    push Not at h
    apply hn
    refine Or.inl (Set.mem_iUnion₂.2 ⟨j 0, Finset.mem_range.2 (by have := hjle 0; simp at this; omega), ?_⟩)
    refine ⟨?_, h⟩
    show P.real (g 0) ≤ s
    linarith [hPg1 0]
  have hstep : ∀ m < M, d (m + 1) - d m < T m := by
    intro m hm
    by_contra h
    push Not at h
    apply hn
    refine Or.inr (Set.mem_iUnion₂.2 ⟨m, Finset.mem_range.2 hm, Set.mem_iUnion₂.2
      ⟨j (m + 1), Finset.mem_range.2 (by have := hjle (m + 1); omega), ?_⟩⟩)
    have hDe : D m (j (m + 1)) = g (m + 1) \ g m := by
      show G ((j (m + 1) : ℝ) * s / 4 ^ (m + 1)) \ G (((j (m + 1) / 4 : ℕ) : ℝ) * s / 4 ^ m) =
        G (b (m + 1)) \ G (b m)
      rw [← hj m]
    show P.real (D m (j (m + 1))) ≤ s / 4 ^ m ∧
      T m ≤ -(cnt (D m (j (m + 1))) S - k * P.real (D m (j (m + 1))))
    rw [hDe, cnt_sdiff (hgg m), measureReal_sdiff (hgg m) (hGm _)]
    refine ⟨by linarith [hPg1 (m + 1), hPg2 m, hb2 m], ?_⟩
    have e : d (m + 1) - d m = -(cnt (g (m + 1)) S - cnt (g m) S -
        k * (P.real (g (m + 1)) - P.real (g m))) := by
      simp only [hddef]; ring
    linarith
  have hfin : k * c - cnt (A u) S ≤ d M + k * s / 4 ^ M := by
    have h1 := cnt_mono (hsub M) S
    have h2 : k * (c - P.real (g M)) ≤ k * (s / 4 ^ M) :=
      mul_le_mul_of_nonneg_left (by linarith [hPg2 M, hb2 M]) hk0
    have e : d M = -(cnt (g M) S - k * P.real (g M)) := rfl
    rw [mul_div_assoc]
    linarith
  have hp := path_total d M _ T hd0 hstep
  have hm := main_arith k s ℓ X M hk0 hs.le hℓ hX hM1 hM2
  have hTe : ∑ m ∈ Finset.range M, T m = ∑ m ∈ Finset.range M,
      (7 / 4 * ((m : ℝ) + 2) * X * (1 / 2) ^ m + 4 * (ℓ + 2 * ((m : ℝ) + 1))) := rfl
  linarith

end OptimalAgnosticPAC.Dev.L33B.PartA
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B
open OptimalAgnosticPAC.Learner
alias chain_lower := OptimalAgnosticPAC.Dev.L33B.PartA.chain_lower

end OptimalAgnosticPAC.Dev.L33B
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
lemma G_le {X : Type} [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    {p : X → ℝ} (hp : Measurable p) (u0 : ℝ) (k : ℕ) {s0 ℓ : ℝ} (hs0 : 0 < s0) (hℓ : 1 ≤ ℓ)
    (i : ℕ) :
    Measure.pi (fun _ : Fin k => P) (G P p u0 k s0 ℓ i) ≤
      ENNReal.ofReal (20 * Real.exp (-ℓ) * Real.exp (-1) ^ i) := by
  have hs : 0 < 2 ^ i * s0 := by positivity
  have hl : 1 ≤ ℓ + i := by have : (0:ℝ) ≤ i := by positivity
                            linarith
  set x := ENNReal.ofReal (5 * Real.exp (-(ℓ + i)))
  have h1 : Measure.pi (fun _ : Fin k => P) (lowEv P (Aset p u0 false) k (2 ^ i * s0) (ℓ + i)) ≤ x :=
    chain_lower P _ (Aset_anti p u0 false) (Aset_meas hp u0 false) k _ _ hs hl
  have h2 : Measure.pi (fun _ : Fin k => P) (upEv P (Aset p u0 true) k (2 ^ i * s0) (ℓ + i)) ≤ x :=
    chain_upper P _ (Aset_anti p u0 true) (Aset_meas hp u0 true) k _ _ hs hl
  have h3 : Measure.pi (fun _ : Fin k => P) (lowEv P (Bset p u0 true) k (2 ^ i * s0) (ℓ + i)) ≤ x :=
    chain_lower P _ (Bset_anti p u0 true) (Bset_meas hp u0 true) k _ _ hs hl
  have h4 : Measure.pi (fun _ : Fin k => P) (upEv P (Bset p u0 false) k (2 ^ i * s0) (ℓ + i)) ≤ x :=
    chain_upper P _ (Bset_anti p u0 false) (Bset_meas hp u0 false) k _ _ hs hl
  calc Measure.pi (fun _ : Fin k => P) (G P p u0 k s0 ℓ i)
      ≤ x + x + x + x := by
        unfold G
        refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2)) h3)) h4)
    _ = ENNReal.ofReal (20 * Real.exp (-ℓ) * Real.exp (-1) ^ i) := by
        have h5 : (0:ℝ) ≤ 5 * Real.exp (-(ℓ + i)) := by positivity
        simp only [x]
        rw [← ENNReal.ofReal_add h5 h5, ← ENNReal.ofReal_add (by positivity) h5,
          ← ENNReal.ofReal_add (by positivity) h5, exp_split]
        congr 1; ring

lemma sum_bound (ℓ : ℝ) :
    ∑' i : ℕ, ENNReal.ofReal (20 * Real.exp (-ℓ) * Real.exp (-1) ^ i) ≤
      ENNReal.ofReal (64 * Real.exp (-ℓ)) := by
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) this
  have hsum : Summable (fun i : ℕ => 20 * Real.exp (-ℓ) * Real.exp (-1) ^ i) :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
  have hinv : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - Real.exp (-1) by linarith)
    rw [inv_eq_one_div]; linarith [show (1:ℝ) / (1 / 2) = 2 by norm_num]
  have he : 0 ≤ Real.exp (-ℓ) := (Real.exp_pos _).le
  nlinarith

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
variable {X : Type}
lemma setsA (p : X → ℝ) {u u0 : ℝ} (hu : u < u0) :
    {z : X × Bool | decide (u ≤ p z.1) ≠ z.2} ∪ Aset p u0 true u =
        {z | decide (u0 ≤ p z.1) ≠ z.2} ∪ Aset p u0 false u ∧
      Disjoint {z : X × Bool | decide (u ≤ p z.1) ≠ z.2} (Aset p u0 true u) ∧
      Disjoint {z : X × Bool | decide (u0 ≤ p z.1) ≠ z.2} (Aset p u0 false u) ∧
      Aset p u0 true u ⊆ {z | decide (u0 ≤ p z.1) ≠ z.2} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨x, b⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, Aset]
    by_cases h1 : u ≤ p x <;> by_cases h2 : u0 ≤ p x <;>
      cases b <;> simp [h1, h2] <;> linarith
  · rw [Set.disjoint_left]; rintro ⟨x, b⟩ h1 ⟨h2, h3, rfl⟩; simp_all
  · rw [Set.disjoint_left]; rintro ⟨x, b⟩ h1 ⟨h2, h3, rfl⟩; simp_all [h3.not_ge]
  · rintro ⟨x, b⟩ ⟨h2, h3, rfl⟩; simp [h3.not_ge]

lemma setsB (p : X → ℝ) {u u0 : ℝ} (hu : u0 ≤ u) :
    {z : X × Bool | decide (u ≤ p z.1) ≠ z.2} ∪ Bset p u0 false (-u) =
        {z | decide (u0 ≤ p z.1) ≠ z.2} ∪ Bset p u0 true (-u) ∧
      Disjoint {z : X × Bool | decide (u ≤ p z.1) ≠ z.2} (Bset p u0 false (-u)) ∧
      Disjoint {z : X × Bool | decide (u0 ≤ p z.1) ≠ z.2} (Bset p u0 true (-u)) ∧
      Bset p u0 false (-u) ⊆ {z | decide (u0 ≤ p z.1) ≠ z.2} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨x, b⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, Bset, neg_neg]
    by_cases h1 : u ≤ p x <;> by_cases h2 : u0 ≤ p x <;>
      cases b <;> simp [h1, h2] <;> linarith
  · rw [Set.disjoint_left]; rintro ⟨x, b⟩ h1 ⟨h2, h3, rfl⟩
    simp only [neg_neg] at h3; simp_all [h3.not_ge]
  · rw [Set.disjoint_left]; rintro ⟨x, b⟩ h1 ⟨h2, h3, rfl⟩; simp_all
  · rintro ⟨x, b⟩ ⟨h2, h3, rfl⟩; simp [h2]

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
lemma bad_sub {X : Type} [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (p : X → ℝ) (hp : Measurable p) (k : ℕ) (hk : 1 ≤ k) (u0 ℓ : ℝ) (hℓ : 1 ≤ ℓ) :
    {S : Fin k → X × Bool | ∃ u : ℝ,
        errCount (fun x => decide (u ≤ p x)) S ≤ errCount (fun x => decide (u0 ≤ p x)) S ∧
        risk P (fun x => decide (u0 ≤ p x)) +
            51280 * (Real.sqrt (risk P (fun x => decide (u0 ≤ p x)) * ℓ / k) + ℓ / k) <
          risk P (fun x => decide (u ≤ p x))} ⊆
      ⋃ i, G P p u0 k (8 * risk P (fun x => decide (u0 ≤ p x)) + 409600 * ℓ / k) ℓ i := by
  rintro S ⟨u, herm, hR⟩
  by_contra hn
  simp only [Set.mem_iUnion, not_exists] at hn
  have herm' : cnt {z : X × Bool | decide (u ≤ p z.1) ≠ z.2} S ≤
      cnt {z : X × Bool | decide (u0 ≤ p z.1) ≠ z.2} S := by
    have h3 : (errCount (fun x => decide (u ≤ p x)) S : ℝ) ≤
        errCount (fun x => decide (u0 ≤ p x)) S := by exact_mod_cast herm
    rw [err_cnt (fun x => decide (u ≤ p x)) S, err_cnt (fun x => decide (u0 ≤ p x)) S] at h3
    exact h3
  simp only [risk] at hR
  rcases lt_or_ge u u0 with hu | hu
  · obtain ⟨hU, h1, h2, hsub⟩ := setsA p hu
    refine absurd hR (not_lt.2 (bridge P hk hℓ S {z | decide (u ≤ p z.1) ≠ z.2}
      {z | decide (u0 ≤ p z.1) ≠ z.2} _ _ (Aset_meas hp u0 false u)
      (Aset_meas hp u0 true u) hU h1 h2 hsub herm' ?_ ?_))
    · intro i hi; by_contra hc; rw [not_le] at hc
      exact hn i (Or.inl (Or.inl (Or.inl ⟨u, hi, hc⟩)))
    · intro i hi; by_contra hc; rw [not_le] at hc
      exact hn i (Or.inl (Or.inl (Or.inr ⟨u, hi, hc⟩)))
  · obtain ⟨hU, h1, h2, hsub⟩ := setsB p hu
    refine absurd hR (not_lt.2 (bridge P hk hℓ S {z | decide (u ≤ p z.1) ≠ z.2}
      {z | decide (u0 ≤ p z.1) ≠ z.2} _ _ (Bset_meas hp u0 true (-u))
      (Bset_meas hp u0 false (-u)) hU h1 h2 hsub herm' ?_ ?_))
    · intro i hi; by_contra hc; rw [not_le] at hc
      exact hn i (Or.inl (Or.inr ⟨-u, hi, hc⟩))
    · intro i hi; by_contra hc; rw [not_le] at hc
      exact hn i (Or.inr ⟨-u, hi, hc⟩)

/-- The ERM bound against one fixed comparator threshold `u0` (Blueprint statement). -/
theorem core {X : Type} [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (p : X → ℝ) (hp : Measurable p) (k : ℕ) (hk : 1 ≤ k) (u0 ℓ : ℝ) (hℓ : 1 ≤ ℓ) :
    Measure.pi (fun _ : Fin k => P)
      {S | ∃ u : ℝ,
        errCount (fun x => decide (u ≤ p x)) S ≤ errCount (fun x => decide (u0 ≤ p x)) S ∧
        risk P (fun x => decide (u0 ≤ p x)) +
            51280 * (Real.sqrt (risk P (fun x => decide (u0 ≤ p x)) * ℓ / k) + ℓ / k) <
          risk P (fun x => decide (u ≤ p x))} ≤
      ENNReal.ofReal (64 * Real.exp (-ℓ)) := by
  have hs0 : 0 < 8 * risk P (fun x => decide (u0 ≤ p x)) + 409600 * ℓ / k := by
    have : 0 ≤ risk P (fun x => decide (u0 ≤ p x)) := measureReal_nonneg
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    positivity
  calc _ ≤ Measure.pi (fun _ : Fin k => P)
        (⋃ i, G P p u0 k (8 * risk P (fun x => decide (u0 ≤ p x)) + 409600 * ℓ / k) ℓ i) :=
        measure_mono (bad_sub P p hp k hk u0 ℓ hℓ)
    _ ≤ ∑' i, Measure.pi (fun _ : Fin k => P)
        (G P p u0 k (8 * risk P (fun x => decide (u0 ≤ p x)) + 409600 * ℓ / k) ℓ i) :=
        measure_iUnion_le _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (20 * Real.exp (-ℓ) * Real.exp (-1) ^ i) :=
        ENNReal.tsum_le_tsum (fun i => G_le P hp u0 k hs0 hℓ i)
    _ ≤ _ := sum_bound ℓ

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B
open OptimalAgnosticPAC.Learner

end OptimalAgnosticPAC.Dev.L33B
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L33B.PartB
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.L33B
lemma mem_T {X : Type} {p : X → ℝ} (hp1 : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) {h : X → Bool}
    (hh : h ∈ thresholdClass p) : ∃ u : ℝ, h = fun x => decide (u ≤ p x) := by
  rcases hh with ⟨u, -, rfl⟩ | hh
  · exact ⟨u, rfl⟩
  · refine ⟨2, ?_⟩
    rw [Set.mem_singleton_iff.1 hh]
    funext x
    have := (hp1 x).2
    simp only [false_eq_decide_iff, not_le]
    linarith

lemma final_arith {L L0 ℓ0 k : ℝ} (hk : 1 ≤ k) (hℓ0 : 0 ≤ ℓ0) (hL : 0 ≤ L)
    (h : L0 < L + ℓ0 / k / 2) :
    L0 + 51280 * (Real.sqrt (L0 * (2 * ℓ0) / k) + 2 * ℓ0 / k) ≤
      L + 223000 * (Real.sqrt (L * ℓ0 / k) + ℓ0 / k) := by
  have hk0 : (0:ℝ) < k := by linarith
  set t := ℓ0 / k with ht
  have ht0 : 0 ≤ t := by positivity
  set a := Real.sqrt (L * ℓ0 / k) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = L * t := by
    rw [ha, Real.sq_sqrt (by positivity), ht]; ring
  have hs : Real.sqrt (L0 * (2 * ℓ0) / k) ≤ 2 * a + t := by
    apply sqrt_le_of (by positivity)
    have : L0 * (2 * ℓ0) / k = 2 * L0 * t := by rw [ht]; ring
    rw [this]
    nlinarith [mul_nonneg ha0 ht0]
  have h2 : 2 * ℓ0 / k = 2 * t := by rw [ht]; ring
  rw [h2]
  have : ℓ0 / k / 2 = t / 2 := by rw [ht]
  nlinarith

end OptimalAgnosticPAC.Dev.L33B.PartB
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Learner
theorem chk_lemma_3_3 {X : Type} [MeasurableSpace X] (P : Measure (X × Bool))
    [IsProbabilityMeasure P] (p : X → ℝ) (hp : Measurable p)
    (hp1 : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k)
    (hhat : (Fin k → X × Bool) → X → Bool) (hERM : IsERM (thresholdClass p) hhat)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sampleLaw P k
      {S | minRisk P (thresholdClass p) +
            223000 * (Real.sqrt (minRisk P (thresholdClass p) * Real.log (12 / δ) / (k : ℝ)) +
              Real.log (12 / δ) / (k : ℝ)) <
          risk P (hhat S)} ≤
      ENNReal.ofReal δ := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hℓ0 : 1 ≤ Real.log (12 / δ) := by
    have h12 : (12:ℝ) ≤ 12 / δ := by rw [le_div_iff₀ hδ0]; nlinarith
    have : (1:ℝ) ≤ Real.log 12 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith [Real.log_le_log (by norm_num) h12]
  have hne : (risk P '' thresholdClass p).Nonempty :=
    ⟨_, ⟨fun _ => false, Or.inr rfl, rfl⟩⟩
  have hbdd : BddBelow (risk P '' thresholdClass p) :=
    ⟨0, by rintro _ ⟨h, -, rfl⟩; exact measureReal_nonneg⟩
  have hL0 : 0 ≤ minRisk P (thresholdClass p) :=
    le_csInf hne (by rintro _ ⟨h, -, rfl⟩; exact measureReal_nonneg)
  have hε : 0 < Real.log (12 / δ) / k / 2 := by positivity
  obtain ⟨_, ⟨h0, hh0, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne hε
  obtain ⟨u0, rfl⟩ := Dev.L33B.PartB.mem_T hp1 hh0
  have hcore := Dev.L33B.PartB.core P p hp k hk u0 (2 * Real.log (12 / δ)) (by linarith)
  unfold sampleLaw
  refine le_trans (measure_mono ?_) (hcore.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro S hS
    obtain ⟨hmem, herm⟩ := hERM S
    obtain ⟨u, hu⟩ := Dev.L33B.PartB.mem_T hp1 hmem
    refine ⟨u, ?_, ?_⟩
    · rw [← hu]; exact herm _ hh0
    · have hS' : minRisk P (thresholdClass p) +
            223000 * (Real.sqrt (minRisk P (thresholdClass p) * Real.log (12 / δ) / (k : ℝ)) +
              Real.log (12 / δ) / (k : ℝ)) < risk P (hhat S) := hS
      rw [hu] at hS'
      have := Dev.L33B.PartB.final_arith (L := minRisk P (thresholdClass p)) hk' (by linarith) hL0 hlt
      linarith
  · have hexp : Real.exp (2 * Real.log (12 / δ)) = (12 / δ) ^ 2 := by
      rw [show 2 * Real.log (12 / δ) = Real.log ((12 / δ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    rw [Real.exp_neg, hexp]
    rw [show 64 * ((12 / δ) ^ 2)⁻¹ = δ * (64 * δ / 144) by field_simp; ring]
    have : 64 * δ / 144 ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
    nlinarith

end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_lemma_3_3 := @OptimalAgnosticPAC.Learner.chk_lemma_3_3
