-- Prove2me | solution 1 for SubsetShrink.BIC.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:12:54.346496+00:00
-- url     : https://prove2.me/submissions/3bb3bb1e-2d29-431b-bf16-9b5b5891b138

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model
import Theorems.Thm_SubsetShrink_BIC_eq_56
import Theorems.Thm_SubsetShrink_BIC_eq_58
import Theorems.Thm_SubsetShrink_BIC_tail_to_expectation

open MeasureTheory ProbabilityTheory
open SubsetShrink.BIC

set_option maxHeartbeats 800000

private lemma log_ep_div_nonneg {p : ℕ} (v : Fin p → ℝ) :
    0 ≤ Real.log (Real.exp 1 * (p : ℝ) / (SubsetShrink.Events.l0 v : ℝ)) := by
  by_cases hk : SubsetShrink.Events.l0 v = 0
  · simp [hk]
  · have hk1 : 1 ≤ SubsetShrink.Events.l0 v := Nat.one_le_iff_ne_zero.mpr hk
    have hkp : SubsetShrink.Events.l0 v ≤ p := by
      rw [SubsetShrink.Events.l0]
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin p)) (fun i => v i ≠ 0)
    have hkR : (0 : ℝ) < (SubsetShrink.Events.l0 v : ℝ) := by exact_mod_cast hk1
    have hkpR : (SubsetShrink.Events.l0 v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hkp
    have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hle : Real.exp 1 ≤ Real.exp 1 * (p : ℝ) / (SubsetShrink.Events.l0 v : ℝ) := by
      rw [le_div_iff₀ hkR]
      exact mul_le_mul_of_nonneg_left hkpR hepos.le
    have h1e : (1 : ℝ) ≤ Real.exp 1 := (Real.one_le_exp_iff).mpr (by norm_num)
    exact Real.log_nonneg (le_trans h1e hle)

private lemma muB_mul_l0_nonneg {p : ℕ} {b : ℝ} (hb : 0 ≤ b) (v : Fin p → ℝ) :
    0 ≤ muB b v * (SubsetShrink.Events.l0 v : ℝ) := by
  rw [muB]
  exact mul_nonneg (mul_nonneg hb (log_ep_div_nonneg v)) (Nat.cast_nonneg _)

private lemma lamB_nonneg {p : ℕ} {a : ℝ} (ha : 0 ≤ a) (v : Fin p → ℝ) : 0 ≤ lamB a v := by
  rw [lamB]
  exact mul_nonneg ha (Real.sqrt_nonneg _)

private lemma l1_nonneg {p : ℕ} (v : Fin p → ℝ) : 0 ≤ SubsetShrink.Events.l1 v := by
  rw [SubsetShrink.Events.l1]
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

private lemma obj2_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (β : Fin p → ℝ) : 0 ≤ obj2 X y a b β := by
  rw [obj2]
  have h1 : 0 ≤ ∑ i, (y i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ lamB a β * SubsetShrink.Events.l2 β :=
    mul_nonneg (lamB_nonneg ha β) (Real.sqrt_nonneg _)
  have h3 : 0 ≤ muB b β * (SubsetShrink.Events.l0 β : ℝ) := muB_mul_l0_nonneg hb β
  linarith

private lemma obj1_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {lam b : ℝ} (hlam : 0 ≤ lam) (hb : 0 ≤ b) (β : Fin p → ℝ) : 0 ≤ obj1 X y lam b β := by
  rw [obj1]
  have h1 : 0 ≤ ∑ i, (y i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ lam * SubsetShrink.Events.l1 β := mul_nonneg hlam (l1_nonneg β)
  have h3 : 0 ≤ muB b β * (SubsetShrink.Events.l0 β : ℝ) := muB_mul_l0_nonneg hb β
  linarith

private lemma le_aux₁ {x M : ℝ} (hx : x ≤ M) (hM0 : 0 ≤ M) :
    x ≤ (M + 1) * (1 + Real.log 2) + 1 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : (0 : ℝ) ≤ M + 1 := by linarith
  have hstep : x ≤ (M + 1) * (1 + Real.log 2) := by
    have hxM : x ≤ M + 1 := le_trans hx (by linarith)
    have := mul_le_mul hxM (by linarith : (1 : ℝ) ≤ 1 + Real.log 2) (by norm_num) hM1
    simpa using this
  linarith

private lemma le_aux₂ {x M : ℝ} (hx : x ≤ M) (hM0 : 0 ≤ M) :
    x * (1 / 2 + Real.log 2) ≤ (M + 1) * (1 + Real.log 2) + 1 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : (0 : ℝ) ≤ M + 1 := by linarith
  have hstep : x * (1 / 2 + Real.log 2) ≤ (M + 1) * (1 + Real.log 2) := by
    have hxM : x ≤ M + 1 := le_trans hx (by linarith)
    exact mul_le_mul hxM (by linarith : (1 : ℝ) / 2 + Real.log 2 ≤ 1 + Real.log 2) (by linarith) hM1
  linarith

private lemma const_step {C C_out or σ2 : ℝ}
    (h1 : C ≤ C_out) (h2 : C * (1 / 2 + Real.log 2) ≤ C_out)
    (hor : 0 ≤ or) (hσ2 : 0 ≤ σ2) :
    C * (or + σ2 * (1 / 2 + Real.log 2)) ≤ C_out * (or + σ2) := by
  have h1' : C * or ≤ C_out * or := mul_le_mul_of_nonneg_right h1 hor
  have h2' : C * (1 / 2 + Real.log 2) * σ2 ≤ C_out * σ2 :=
    mul_le_mul_of_nonneg_right h2 hσ2
  calc C * (or + σ2 * (1 / 2 + Real.log 2))
      = C * or + C * (1 / 2 + Real.log 2) * σ2 := by ring
    _ ≤ C_out * or + C_out * σ2 := add_le_add h1' h2'
    _ = C_out * (or + σ2) := by ring

private lemma expectation_from_tail {n : ℕ} (σ : ℝ) (hσ : 0 < σ) (C : ℝ) (hC : 0 < C)
    (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (oracle : ℝ) (horacle : 0 ≤ oracle)
    (hprob : ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
      1 - δ0 / 2 ≤ (SubsetShrink.Events.noiseLaw n σ
        {ε | g ε ≤ C * (oracle + σ ^ 2 * Real.log (2 / δ0))}).toReal) :
    ∫⁻ ε, ENNReal.ofReal (g ε) ∂(SubsetShrink.Events.noiseLaw n σ) ≤
      ENNReal.ofReal (C * (oracle + σ ^ 2 * (1 / 2 + Real.log 2))) := by
  haveI hmup : IsProbabilityMeasure (SubsetShrink.Events.noiseLaw n σ) := by
    haveI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
      fun _ => ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩
    rw [SubsetShrink.Events.noiseLaw]
    infer_instance
  have hD : 0 < C * σ ^ 2 := mul_pos hC (pow_pos hσ 2)
  set Wt : (Fin n → ℝ) → ℝ := fun ε => (g ε - C * oracle) / (C * σ ^ 2) - Real.log 2 with hWtdef
  have hWt_meas : Measurable Wt := by
    rw [hWtdef]
    exact ((hg.sub measurable_const).div_const _).sub measurable_const
  have hhyp : ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
      1 - δ0 / 2 ≤ ((SubsetShrink.Events.noiseLaw n σ)
        {ω : Fin n → ℝ | Wt ω ≤ 1 * Real.log (1 / δ0)}).toReal := by
    intro δ0 h0 h1
    have hlogA : Real.log (2 / δ0) = Real.log (1 / δ0) + Real.log 2 := by
      have h : (2 : ℝ) / δ0 = 2 * (1 / δ0) := by ring
      rw [h, Real.log_mul (by norm_num) (by positivity)]
      ring
    have hset : {ω : Fin n → ℝ | Wt ω ≤ 1 * Real.log (1 / δ0)}
        = {ε : Fin n → ℝ | g ε ≤ C * (oracle + σ ^ 2 * Real.log (2 / δ0))} := by
      ext ε
      simp only [Set.mem_setOf_eq, one_mul, hWtdef]
      rw [hlogA]
      constructor
      · intro hle
        have e1 : (g ε - C * oracle) / (C * σ ^ 2) ≤ Real.log (1 / δ0) + Real.log 2 := by
          linarith
        have e2 := (div_le_iff₀ hD).mp e1
        nlinarith [e2]
      · intro hle
        have e2 : g ε - C * oracle ≤ (Real.log (1 / δ0) + Real.log 2) * (C * σ ^ 2) := by
          nlinarith [hle]
        have e1 := (div_le_iff₀ hD).mpr e2
        linarith
    rw [hset]
    exact hprob δ0 h0 h1
  have hbound : ∫⁻ ω, ENNReal.ofReal (Wt ω) ∂(SubsetShrink.Events.noiseLaw n σ)
      ≤ ENNReal.ofReal (1 / 2) :=
    (SubsetShrink.BIC.tail_to_expectation (SubsetShrink.Events.noiseLaw n σ) Wt hWt_meas 1
      (by norm_num) hhyp).2
  have hpoint : ∀ ε, ENNReal.ofReal (g ε)
      ≤ ENNReal.ofReal (C * σ ^ 2) * ENNReal.ofReal (Wt ε)
        + ENNReal.ofReal (C * σ ^ 2 * Real.log 2 + C * oracle) := by
    intro ε
    have hgeq : g ε = C * σ ^ 2 * Wt ε + (C * σ ^ 2 * Real.log 2 + C * oracle) := by
      rw [hWtdef]
      field_simp
      ring
    calc ENNReal.ofReal (g ε)
        = ENNReal.ofReal (C * σ ^ 2 * Wt ε + (C * σ ^ 2 * Real.log 2 + C * oracle)) := by
          rw [hgeq]
      _ ≤ ENNReal.ofReal (C * σ ^ 2 * Wt ε)
            + ENNReal.ofReal (C * σ ^ 2 * Real.log 2 + C * oracle) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (C * σ ^ 2) * ENNReal.ofReal (Wt ε)
            + ENNReal.ofReal (C * σ ^ 2 * Real.log 2 + C * oracle) := by
          rw [ENNReal.ofReal_mul hD.le]
  have hmeas_f : Measurable (fun ε => ENNReal.ofReal (C * σ ^ 2) * ENNReal.ofReal (Wt ε)) :=
    (Measurable.ennreal_ofReal hWt_meas).const_mul _
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb1 : 0 ≤ C * σ ^ 2 * (1 / 2) := by positivity
  have hb2 : 0 ≤ C * σ ^ 2 * Real.log 2 + C * oracle := by
    have hb2a : 0 ≤ C * σ ^ 2 * Real.log 2 := mul_nonneg hD.le hlog2pos.le
    have hb2b : 0 ≤ C * oracle := mul_nonneg hC.le horacle
    linarith
  calc ∫⁻ ε, ENNReal.ofReal (g ε) ∂(SubsetShrink.Events.noiseLaw n σ)
      ≤ ∫⁻ ε, (ENNReal.ofReal (C * σ ^ 2) * ENNReal.ofReal (Wt ε)
          + ENNReal.ofReal (C * σ ^ 2 * Real.log 2 + C * oracle))
          ∂(SubsetShrink.Events.noiseLaw n σ) := lintegral_mono hpoint
    _ = (∫⁻ ε, ENNReal.ofReal (C * σ ^ 2) * ENNReal.ofReal (Wt ε)
            ∂(SubsetShrink.Events.noiseLaw n σ))
          + ENNReal.ofReal (C * σ ^ 2 * Real.log 2 + C * oracle) := by
          rw [lintegral_add_left hmeas_f, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (C * σ ^ 2) * ENNReal.ofReal (1 / 2)
          + ENNReal.ofReal (C * σ ^ 2 * Real.log 2 + C * oracle) := by
          rw [lintegral_const_mul _ (Measurable.ennreal_ofReal hWt_meas)]
          exact add_le_add (mul_le_mul_of_nonneg_left hbound
            (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal (C * σ ^ 2))) le_rfl
    _ = ENNReal.ofReal (C * (oracle + σ ^ 2 * (1 / 2 + Real.log 2))) := by
          rw [← ENNReal.ofReal_mul (p := C * σ ^ 2) (q := 1 / 2) hD.le,
            ← ENNReal.ofReal_add hb1 hb2]
          congr 1
          ring

theorem solution :
    ∃ a0 b0 c0 C : ℝ, 0 < C ∧
      (∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ a b : ℝ)
        (βhat : (Fin n → ℝ) → (Fin p → ℝ)),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ a → 0 ≤ b → (a0 * σ ≤ a ∨ b0 * σ ^ 2 ≤ b) →
        Measurable βhat → (∀ y, IsBIC2 X y a b (βhat y)) →
        ∀ β : Fin p → ℝ,
          ∫⁻ ε, ENNReal.ofReal (∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
              ∂(SubsetShrink.Events.noiseLaw n σ) ≤
            ENNReal.ofReal (C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lamB a β * SubsetShrink.Events.l2 β +
              muB b β * (SubsetShrink.Events.l0 β : ℝ) + σ ^ 2))) ∧
      (∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ lam b : ℝ)
        (βhat : (Fin n → ℝ) → (Fin p → ℝ)),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ lam → 0 ≤ b →
        (c0 * σ * Real.sqrt (Real.log (Real.exp 1 * p)) ≤ lam ∨ b0 * σ ^ 2 ≤ b) →
        Measurable βhat → (∀ y, IsBIC1 X y lam b (βhat y)) →
        ∀ β : Fin p → ℝ,
          ∫⁻ ε, ENNReal.ofReal (∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
              ∂(SubsetShrink.Events.noiseLaw n σ) ≤
            ENNReal.ofReal (C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lam * SubsetShrink.Events.l1 β +
              muB b β * (SubsetShrink.Events.l0 β : ℝ) + σ ^ 2))) := by
  obtain ⟨a0, b0, C, hCpos, h56⟩ := SubsetShrink.BIC.eq_56
  obtain ⟨c0, b0', C', hC'pos, h58⟩ := SubsetShrink.BIC.eq_58
  refine ⟨a0, max b0 b0', c0, (max C C' + 1) * (1 + Real.log 2) + 1, ?_, ?_, ?_⟩
  · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hm1 : (0 : ℝ) < max C C' + 1 := by
      have := le_max_left C C'
      linarith
    have hm2 : (0 : ℝ) < 1 + Real.log 2 := by linarith
    have := mul_pos hm1 hm2
    linarith
  · intro n p X fstar σ a b βhat hUC h1p hσ ha hb hdisj hβmeas hβmin β
    haveI hmup : IsProbabilityMeasure (SubsetShrink.Events.noiseLaw n σ) := by
      haveI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
        fun _ => ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩
      rw [SubsetShrink.Events.noiseLaw]
      infer_instance
    set oracle : ℝ := ∑ i, (fstar i - X.mulVec β i) ^ 2 + lamB a β * SubsetShrink.Events.l2 β
        + muB b β * (SubsetShrink.Events.l0 β : ℝ) with horacle_def
    have hm : C ≤ max C C' := le_max_left C C'
    have hM0 : 0 ≤ max C C' := le_trans hCpos.le hm
    have h1 : C ≤ (max C C' + 1) * (1 + Real.log 2) + 1 := le_aux₁ hm hM0
    have h2 : C * (1 / 2 + Real.log 2) ≤ (max C C' + 1) * (1 + Real.log 2) + 1 := le_aux₂ hm hM0
    have hor : 0 ≤ oracle := by rw [horacle_def]; exact obj2_nonneg X fstar ha hb β
    have hdisj56 : a0 * σ ≤ a ∨ b0 * σ ^ 2 ≤ b := by
      rcases hdisj with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (mul_le_mul_of_nonneg_right (le_max_left b0 b0') (sq_nonneg σ)) h)
    have hg_meas : Measurable (fun ε : Fin n → ℝ =>
        ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2) := by
      have hmv : Measurable (fun v : Fin p → ℝ => X.mulVec v) := by fun_prop
      have hcomp : Measurable (fun ε : Fin n → ℝ => X.mulVec (βhat (fstar + ε))) :=
        hmv.comp (hβmeas.comp (measurable_const.add measurable_id))
      exact Finset.measurable_sum _ (fun i _ =>
        (measurable_const.sub ((measurable_pi_apply i).comp hcomp)).pow_const 2)
    have hprob : ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
        1 - δ0 / 2 ≤ (SubsetShrink.Events.noiseLaw n σ
          {ε : Fin n → ℝ | ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2
            ≤ C * (oracle + σ ^ 2 * Real.log (2 / δ0))}).toReal := by
      intro δ0 hδ0 hδ0lt
      have hδ0half_pos : 0 < δ0 / 2 := by linarith
      have hδ0half_lt : δ0 / 2 < 1 := by linarith
      obtain ⟨A, _hAmeas, hAprob, hAon⟩ :=
        h56 X fstar σ a b (δ0 / 2) hUC h1p hσ ha hb hdisj56 hδ0half_pos hδ0half_lt
      have hloghalf : Real.log (1 / (δ0 / 2)) = Real.log (2 / δ0) := by
        congr 1
        rw [one_div, inv_div]
      have hsub : A ⊆ {ε : Fin n → ℝ |
          ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2
            ≤ C * (oracle + σ ^ 2 * Real.log (2 / δ0))} := by
        intro ε hε
        have hh := hAon ε hε (βhat (fstar + ε)) (hβmin (fstar + ε)) β
        rw [hloghalf, ← horacle_def] at hh
        have h2' : 0 ≤ muB b (βhat (fstar + ε))
            * (SubsetShrink.Events.l0 (βhat (fstar + ε)) : ℝ) := muB_mul_l0_nonneg hb _
        simp only [Set.mem_setOf_eq]
        linarith
      calc 1 - δ0 / 2 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal := hAprob
        _ ≤ (SubsetShrink.Events.noiseLaw n σ {ε : Fin n → ℝ |
              ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2
                ≤ C * (oracle + σ ^ 2 * Real.log (2 / δ0))}).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have hmain := expectation_from_tail σ hσ C hCpos
      (fun ε : Fin n → ℝ => ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
      hg_meas oracle hor hprob
    calc ∫⁻ ε, ENNReal.ofReal (∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
            ∂(SubsetShrink.Events.noiseLaw n σ)
        ≤ ENNReal.ofReal (C * (oracle + σ ^ 2 * (1 / 2 + Real.log 2))) := hmain
      _ ≤ ENNReal.ofReal (((max C C' + 1) * (1 + Real.log 2) + 1) * (oracle + σ ^ 2)) :=
          ENNReal.ofReal_le_ofReal (const_step h1 h2 hor (sq_nonneg σ))

  · intro n p X fstar σ lam b βhat hUC h1p hσ hlam hb hdisj hβmeas hβmin β
    haveI hmup : IsProbabilityMeasure (SubsetShrink.Events.noiseLaw n σ) := by
      haveI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
        fun _ => ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩
      rw [SubsetShrink.Events.noiseLaw]
      infer_instance
    set oracle : ℝ := ∑ i, (fstar i - X.mulVec β i) ^ 2 + lam * SubsetShrink.Events.l1 β
        + muB b β * (SubsetShrink.Events.l0 β : ℝ) with horacle_def
    have hm : C' ≤ max C C' := le_max_right C C'
    have hM0 : 0 ≤ max C C' := le_trans hC'pos.le hm
    have h1 : C' ≤ (max C C' + 1) * (1 + Real.log 2) + 1 := le_aux₁ hm hM0
    have h2 : C' * (1 / 2 + Real.log 2) ≤ (max C C' + 1) * (1 + Real.log 2) + 1 := le_aux₂ hm hM0
    have hor : 0 ≤ oracle := by rw [horacle_def]; exact obj1_nonneg X fstar hlam hb β
    have hdisj58 : c0 * σ * Real.sqrt (Real.log (Real.exp 1 * p)) ≤ lam ∨ b0' * σ ^ 2 ≤ b := by
      rcases hdisj with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (mul_le_mul_of_nonneg_right (le_max_right b0 b0') (sq_nonneg σ)) h)
    have hg_meas : Measurable (fun ε : Fin n → ℝ =>
        ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2) := by
      have hmv : Measurable (fun v : Fin p → ℝ => X.mulVec v) := by fun_prop
      have hcomp : Measurable (fun ε : Fin n → ℝ => X.mulVec (βhat (fstar + ε))) :=
        hmv.comp (hβmeas.comp (measurable_const.add measurable_id))
      exact Finset.measurable_sum _ (fun i _ =>
        (measurable_const.sub ((measurable_pi_apply i).comp hcomp)).pow_const 2)
    have hprob : ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
        1 - δ0 / 2 ≤ (SubsetShrink.Events.noiseLaw n σ
          {ε : Fin n → ℝ | ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2
            ≤ C' * (oracle + σ ^ 2 * Real.log (2 / δ0))}).toReal := by
      intro δ0 hδ0 hδ0lt
      have hδ0half_pos : 0 < δ0 / 2 := by linarith
      have hδ0half_lt : δ0 / 2 < 1 := by linarith
      obtain ⟨A, _hAmeas, hAprob, hAon⟩ :=
        h58 X fstar σ lam b (δ0 / 2) hUC h1p hσ hlam hb hdisj58 hδ0half_pos hδ0half_lt
      have hloghalf : Real.log (1 / (δ0 / 2)) = Real.log (2 / δ0) := by
        congr 1
        rw [one_div, inv_div]
      have hsub : A ⊆ {ε : Fin n → ℝ |
          ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2
            ≤ C' * (oracle + σ ^ 2 * Real.log (2 / δ0))} := by
        intro ε hε
        have hh := hAon ε hε (βhat (fstar + ε)) (hβmin (fstar + ε)) β
        rw [hloghalf, ← horacle_def] at hh
        have h2' : 0 ≤ muB b (βhat (fstar + ε))
            * (SubsetShrink.Events.l0 (βhat (fstar + ε)) : ℝ) := muB_mul_l0_nonneg hb _
        simp only [Set.mem_setOf_eq]
        linarith
      calc 1 - δ0 / 2 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal := hAprob
        _ ≤ (SubsetShrink.Events.noiseLaw n σ {ε : Fin n → ℝ |
              ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2
                ≤ C' * (oracle + σ ^ 2 * Real.log (2 / δ0))}).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have hmain := expectation_from_tail σ hσ C' hC'pos
      (fun ε : Fin n → ℝ => ∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
      hg_meas oracle hor hprob
    calc ∫⁻ ε, ENNReal.ofReal (∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
            ∂(SubsetShrink.Events.noiseLaw n σ)
        ≤ ENNReal.ofReal (C' * (oracle + σ ^ 2 * (1 / 2 + Real.log 2))) := hmain
      _ ≤ ENNReal.ofReal (((max C C' + 1) * (1 + Real.log 2) + 1) * (oracle + σ ^ 2)) :=
          ENNReal.ofReal_le_ofReal (const_step h1 h2 hor (sq_nonneg σ))
