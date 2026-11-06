-- Prove2me | solution 1 for ProbMetricStab.MixedInt.growth_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:53:02.571845+00:00
-- url     : https://prove2.me/submissions/40c6cc2c-b561-498a-8dcf-c2822b5c6ebd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
import Theorems.Thm_ProbMetricStab_MixedInt_lemma_3_5_b

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt.GrowthAux

open ProbMetricStab.MixedInt

/-- An affine map on a finite-dimensional space has affine growth. -/
lemma affine_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ᵃ[ℝ] F) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ ξ, ‖f ξ‖ ≤ a + b * ‖ξ‖ := by
  refine ⟨‖f 0‖, ‖LinearMap.toContinuousLinearMap f.linear‖, norm_nonneg _, norm_nonneg _,
    fun ξ => ?_⟩
  have h1 : f ξ = f.linear ξ + f 0 := by
    have := f.linearMap_vsub ξ 0
    simp only [vsub_eq_sub, sub_zero] at this
    rw [this]; abel
  have h2 : ‖f.linear ξ‖ ≤ ‖LinearMap.toContinuousLinearMap f.linear‖ * ‖ξ‖ :=
    (LinearMap.toContinuousLinearMap f.linear).le_opNorm ξ
  calc ‖f ξ‖ ≤ ‖f.linear ξ‖ + ‖f 0‖ := by rw [h1]; exact norm_add_le _ _
    _ ≤ _ := by linarith

/-- `∫ (A + B‖ξ‖) dν < ∞` for a probability measure with finite first moment. -/
lemma lintegral_affine_lt_top {s : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin s)))
    [IsProbabilityMeasure ν] (hν : ∫⁻ ξ, ENNReal.ofReal ‖ξ‖ ∂ν < ∞) (A B : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (A + B * ‖ξ‖) ∂ν < ∞ := by
  have hle : ∀ ξ : EuclideanSpace ℝ (Fin s), ENNReal.ofReal (A + B * ‖ξ‖) ≤
      (fun _ => ENNReal.ofReal A) ξ + ENNReal.ofReal B * ENNReal.ofReal ‖ξ‖ := by
    intro ξ
    calc ENNReal.ofReal (A + B * ‖ξ‖) ≤ ENNReal.ofReal A + ENNReal.ofReal (B * ‖ξ‖) :=
          ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal ‖ξ‖ := by
          gcongr
          rcases le_or_gt 0 B with hB | hB
          · rw [ENNReal.ofReal_mul hB]
          · rw [ENNReal.ofReal_of_nonpos (by nlinarith [norm_nonneg ξ])]; exact bot_le
  calc ∫⁻ ξ, ENNReal.ofReal (A + B * ‖ξ‖) ∂ν
      ≤ ∫⁻ ξ, ((fun _ => ENNReal.ofReal A) ξ + ENNReal.ofReal B * ENNReal.ofReal ‖ξ‖) ∂ν :=
        lintegral_mono hle
    _ = ∫⁻ _, ENNReal.ofReal A ∂ν + ENNReal.ofReal B * ∫⁻ ξ, ENNReal.ofReal ‖ξ‖ ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul _ measurable_norm.ennreal_ofReal]
    _ < ∞ := by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν⟩

lemma coe_sub_coe {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal ha, EReal.coe_ennreal_toReal hb]

end ProbMetricStab.MixedInt.GrowthAux

open ProbMetricStab.MixedInt ProbMetricStab.MixedInt.GrowthAux in
theorem solution {m s r mh mb : ℕ} (P : ProbMetricStab.MixedInt.MIProgram m s r mh mb)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      (∀ t ∈ P.recourse.Tset, ∀ t' ∈ P.recourse.Tset,
        |(P.recourse.Phi t).toReal - (P.recourse.Phi t').toReal| ≤ α * ‖t - t'‖ + β) ∧
      (∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.f0 ξ x ≠ ⊤ ∧ P.f0 ξ x ≠ ⊥ ∧
        |(P.f0 ξ x).toReal| ≤ ‖P.c‖ * ‖x‖ + α * (‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖) + β) ∧
      (∀ U : Set (EuclideanSpace ℝ (Fin m)), Bornology.IsBounded U →
        Pp P.Ξ 1 ⊆ PFU P.Ξ P.f0 P.X U) := by
  classical
  obtain ⟨hfin, -, α, β, hα, hβ, hΦ⟩ := lemma_3_5_b P.recourse hB1 hB3
  have h0T : (0 : EuclideanSpace ℝ (Fin r)) ∈ P.recourse.Tset :=
    ⟨0, 0, le_rfl, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  set β' := β + |(P.recourse.Phi 0).toReal| with hβ'
  have hβ'pos : 0 < β' := by positivity
  have hΦ' : ∀ t ∈ P.recourse.Tset, ∀ t' ∈ P.recourse.Tset,
      |(P.recourse.Phi t).toReal - (P.recourse.Phi t').toReal| ≤ α * ‖t - t'‖ + β' := by
    intro t ht t' ht'
    have := hΦ t ht t' ht'
    have : 0 ≤ |(P.recourse.Phi 0).toReal| := abs_nonneg _
    linarith
  have hΦb : ∀ t ∈ P.recourse.Tset, |(P.recourse.Phi t).toReal| ≤ α * ‖t‖ + β' := by
    intro t ht
    have h1 := hΦ t ht 0 h0T
    rw [sub_zero] at h1
    have h2 := abs_sub_abs_le_abs_sub (P.recourse.Phi t).toReal (P.recourse.Phi 0).toReal
    rw [hβ']; linarith
  -- pointwise facts on `f₀`
  have hf0 : ∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.f0 ξ x ≠ ⊤ ∧ P.f0 ξ x ≠ ⊥ ∧
      P.f0 ξ x = (((P.f0 ξ x).toReal : ℝ) : EReal) ∧
      |(P.f0 ξ x).toReal| ≤ ‖P.c‖ * ‖x‖ + α * (‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖) + β' := by
    intro ξ hξ x hx
    have ht := hB2 ξ hξ x hx
    obtain ⟨hne1, hne2⟩ := hfin _ ht
    have hval : P.f0 ξ x = ((inner ℝ P.c x + (P.recourse.Phi (P.h ξ - P.T ξ x)).toReal : ℝ) :
        EReal) := by
      unfold MIProgram.f0
      rw [EReal.coe_add, EReal.coe_toReal hne1 hne2]
    rw [hval, EReal.toReal_coe]
    refine ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _, rfl, ?_⟩
    have h1 : |inner ℝ P.c x| ≤ ‖P.c‖ * ‖x‖ := abs_real_inner_le_norm _ _
    have h2 := hΦb _ ht
    have h3 : ‖P.h ξ - P.T ξ x‖ ≤ ‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖ :=
      (norm_sub_le _ _).trans (by gcongr; exact (P.T ξ).le_opNorm x)
    calc |inner ℝ P.c x + (P.recourse.Phi (P.h ξ - P.T ξ x)).toReal|
        ≤ |inner ℝ P.c x| + |(P.recourse.Phi (P.h ξ - P.T ξ x)).toReal| := abs_add_le _ _
      _ ≤ ‖P.c‖ * ‖x‖ + (α * ‖P.h ξ - P.T ξ x‖ + β') := add_le_add h1 h2
      _ ≤ _ := by nlinarith
  obtain ⟨ah, bh, hah, hbh, hhb⟩ := affine_bound P.h
  obtain ⟨aT, bT, haT, hbT, hTb⟩ := affine_bound P.T
  -- uniform bound on `‖x‖ ≤ ρ`
  have hM : ∀ ρ : ℝ, 0 ≤ ρ → ∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, ‖x‖ ≤ ρ →
      |(P.f0 ξ x).toReal| ≤ (‖P.c‖ * ρ + α * ah + α * aT * ρ + β') +
        (α * bh + α * bT * ρ) * ‖ξ‖ := by
    intro ρ hρ ξ hξ x hx hxρ
    have h1 := (hf0 ξ hξ x hx).2.2.2
    have h2 := hhb ξ
    have h3 := hTb ξ
    have hc := norm_nonneg P.c
    have hTn := norm_nonneg (P.T ξ)
    have hxn := norm_nonneg x
    have hξn := norm_nonneg ξ
    have e1 : ‖P.c‖ * ‖x‖ ≤ ‖P.c‖ * ρ := mul_le_mul_of_nonneg_left hxρ hc
    have e2 : ‖P.T ξ‖ * ‖x‖ ≤ (aT + bT * ‖ξ‖) * ρ :=
      mul_le_mul h3 hxρ hxn (by positivity)
    have e3 : α * (‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖) ≤ α * ((ah + bh * ‖ξ‖) + (aT + bT * ‖ξ‖) * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) hα.le
    nlinarith
  refine ⟨α, β', hα, hβ'pos, hΦ', fun ξ hξ x hx => ⟨(hf0 ξ hξ x hx).1, (hf0 ξ hξ x hx).2.1,
    (hf0 ξ hξ x hx).2.2.2⟩, ?_⟩
  intro U hU ν hν
  obtain ⟨⟨hprob, hν0⟩, hmom⟩ := hν
  have : IsProbabilityMeasure ν := hprob
  simp only [Real.rpow_one] at hmom
  have hae : ∀ᵐ ξ ∂ν, ξ ∈ P.Ξ := by
    rw [ae_iff]
    exact hν0
  refine ⟨⟨hprob, hν0⟩, ?_, ?_⟩
  · intro ρ hρ
    set A := ‖P.c‖ * ρ + α * ah + α * aT * ρ + β'
    set B := α * bh + α * bT * ρ
    have hneg : ∀ᵐ ξ ∂ν, (-(⨅ x ∈ P.X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ,
        P.f0 ξ x)).toENNReal ≤ ENNReal.ofReal (A + B * ‖ξ‖) := by
      filter_upwards [hae] with ξ hξ
      have hge : ((-(A + B * ‖ξ‖) : ℝ) : EReal) ≤
          ⨅ x ∈ P.X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ, P.f0 ξ x := by
        refine le_iInf₂ fun x hx => ?_
        have hxρ : ‖x‖ ≤ ρ := by simpa using hx.2
        have hb := hM ρ hρ.le ξ hξ x hx.1 hxρ
        rw [(hf0 ξ hξ x hx.1).2.2.1]
        exact EReal.coe_le_coe_iff.2 (by linarith [neg_abs_le (P.f0 ξ x).toReal])
      have : -(⨅ x ∈ P.X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ, P.f0 ξ x) ≤
          ((A + B * ‖ξ‖ : ℝ) : EReal) := by
        rw [EReal.neg_le, ← EReal.coe_neg]; exact hge
      calc _ ≤ (((A + B * ‖ξ‖ : ℝ) : EReal)).toENNReal := EReal.toENNReal_le_toENNReal this
        _ = ENNReal.ofReal (A + B * ‖ξ‖) := by
          rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    have hfinneg := (lintegral_mono_ae hneg).trans_lt (lintegral_affine_lt_top ν hmom A B)
    unfold DupacovaWets.Consistency.expect
    split_ifs with htop
    · exact bot_lt_top
    · rw [coe_sub_coe htop hfinneg.ne]
      exact EReal.bot_lt_coe _
  · obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hU.closure
    set R' := max R 0
    set A := ‖P.c‖ * R' + α * ah + α * aT * R' + β'
    set B := α * bh + α * bT * R'
    have hfinI := lintegral_affine_lt_top ν hmom A B
    refine lt_of_le_of_lt (b := ((∫⁻ ξ, ENNReal.ofReal (A + B * ‖ξ‖) ∂ν : ℝ≥0∞) : EReal))
      (iSup₂_le fun x hx => ?_) (by
        rw [← EReal.coe_ennreal_toReal hfinI.ne]; exact EReal.coe_lt_top _)
    have hxR : ‖x‖ ≤ R' := (hR x hx.2).trans (le_max_left _ _)
    have hpos : ∀ᵐ ξ ∂ν, (P.f0 ξ x).toENNReal ≤ ENNReal.ofReal (A + B * ‖ξ‖) := by
      filter_upwards [hae] with ξ hξ
      have hb := hM R' (le_max_right _ _) ξ hξ x hx.1 hxR
      rw [(hf0 ξ hξ x hx.1).2.2.1, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
        EReal.toReal_coe]
      exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (P.f0 ξ x).toReal])
    have hposI := lintegral_mono_ae hpos
    unfold intObj DupacovaWets.Consistency.expect
    split_ifs with htop
    · exact absurd htop (hposI.trans_lt hfinI).ne
    · have hn2 : ∫⁻ ξ, (-(P.f0 ξ x)).toENNReal ∂ν ≠ ∞ ∨ True := Or.inr trivial
      clear hn2
      by_cases hneg : ∫⁻ ξ, (-(P.f0 ξ x)).toENNReal ∂ν = ∞
      · rw [hneg]
        have : ((∫⁻ ξ, (P.f0 ξ x).toENNReal ∂ν : ℝ≥0∞) : EReal) - ((⊤ : ℝ≥0∞) : EReal) = ⊥ := by
          rw [← EReal.coe_ennreal_toReal htop]
          simp
        rw [this]; exact bot_le
      · rw [coe_sub_coe htop hneg]
        have h1 : ((∫⁻ ξ, (P.f0 ξ x).toENNReal ∂ν).toReal -
            (∫⁻ ξ, (-(P.f0 ξ x)).toENNReal ∂ν).toReal : ℝ) ≤
            (∫⁻ ξ, ENNReal.ofReal (A + B * ‖ξ‖) ∂ν).toReal := by
          have := ENNReal.toReal_mono hfinI.ne hposI
          linarith [ENNReal.toReal_nonneg (a := ∫⁻ ξ, (-(P.f0 ξ x)).toENNReal ∂ν)]
        rw [← EReal.coe_ennreal_toReal hfinI.ne]
        exact EReal.coe_le_coe_iff.2 h1
