-- Prove2me | solution 1 for RobustLP.Counterpart.symmetric_sum_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T03:18:29.418424+00:00
-- url     : https://prove2.me/submissions/2071721d-29e7-4f8c-b822-5aa830027531

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {ι : Type*} [Fintype ι]
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (η : ι → S → ℝ) (hmeas : ∀ j, Measurable (η j)) (hindep : iIndepFun η P)
    (hsymm : ∀ j, P.map (η j) = P.map (fun ω => -η j ω))
    (hbdd : ∀ j ω, η j ω ∈ Set.Icc (-1 : ℝ) 1)
    (pc : ι → ℝ) (Ω : ℝ) (hΩ : 0 < Ω) :
    P.real {ω | Ω * Real.sqrt (∑ j, pc j ^ 2) < ∑ j, η j ω * pc j} ≤
      Real.exp (-(Ω ^ 2 / 2)) := by
  classical
  set Sq : ℝ := ∑ j, pc j ^ 2 with hSq
  have hSqnn : 0 ≤ Sq := by
    rw [hSq]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the degenerate case
  rcases eq_or_lt_of_le hSqnn with hzero | hpos
  · -- all `pc j` vanish, so the event is empty
    have hall : ∀ j, pc j = 0 := by
      intro j
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (pc j))).mp (by rw [hSq] at hzero; exact hzero.symm) j
        (Finset.mem_univ j)
      exact pow_eq_zero_iff (by norm_num) |>.mp h
    have hempty : {ω | Ω * Real.sqrt Sq < ∑ j, η j ω * pc j} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : ∑ j, η j ω * pc j = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hall j, mul_zero]
      rw [h1, ← hzero]
      simp
    rw [hempty]
    simp only [measureReal_empty]
    positivity
  -- the main case
  have hSqpos : 0 < Sq := hpos
  set X : ι → S → ℝ := fun j ω => η j ω * pc j with hX
  have hXmeas : ∀ j, Measurable (X j) := fun j => (hmeas j).mul_const _
  have hint : ∀ j, Integrable (η j) P :=
    fun j => Integrable.of_mem_Icc (-1) 1 (hmeas j).aemeasurable (ae_of_all _ (hbdd j))
  have hmean : ∀ j, ∫ ω, η j ω ∂P = 0 := by
    intro j
    have h1 : ∫ x, x ∂(P.map (η j)) = ∫ ω, η j ω ∂P :=
      integral_map (hmeas j).aemeasurable aestronglyMeasurable_id
    have h2 : ∫ x, x ∂(P.map (fun ω => -η j ω)) = ∫ ω, -η j ω ∂P :=
      integral_map ((hmeas j).neg).aemeasurable aestronglyMeasurable_id
    have h3 : ∫ ω, η j ω ∂P = ∫ ω, -η j ω ∂P := by
      rw [← h1, ← h2, hsymm j]
    rw [integral_neg] at h3
    linarith
  have hXmean : ∀ j, ∫ ω, X j ω ∂P = 0 := by
    intro j
    simp only [hX]
    rw [integral_mul_const, hmean j, zero_mul]
  have hXbdd : ∀ j, ∀ᵐ ω ∂P, X j ω ∈ Set.Icc (-|pc j|) (|pc j|) := by
    intro j
    refine ae_of_all _ fun ω => ?_
    obtain ⟨h1, h2⟩ := hbdd j ω
    have habs : |η j ω| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
    have : |X j ω| ≤ |pc j| := by
      simp only [hX, abs_mul]
      calc |η j ω| * |pc j| ≤ 1 * |pc j| :=
            mul_le_mul_of_nonneg_right habs (abs_nonneg _)
        _ = |pc j| := one_mul _
    exact abs_le.mp this |>.imp id id
  set c : ι → NNReal := fun j => (‖|pc j| - -|pc j|‖₊ / 2) ^ 2 with hc
  have hcval : ∀ j, ((c j : ℝ)) = pc j ^ 2 := by
    intro j
    simp only [hc]
    push_cast
    have h2 : ‖|pc j| - -|pc j|‖ = 2 * |pc j| := by
      rw [Real.norm_eq_abs]
      have h4 : |pc j| - -|pc j| = 2 * |pc j| := by ring
      rw [h4, abs_of_nonneg (by positivity)]
    rw [h2]
    have h3 : (2 * |pc j| / 2) = |pc j| := by ring
    rw [h3, sq_abs]
  have hsubG : ∀ j : ι, j ∈ Finset.univ → HasSubgaussianMGF (X j) (c j) P := by
    intro j _
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hXmeas j).aemeasurable
      (hXbdd j) (hXmean j)
  have hXindep : iIndepFun X P := by
    have h := hindep.comp (fun j => fun x : ℝ => x * pc j) (fun j => measurable_id.mul_const _)
    exact h
  have hcsum : ((∑ j, c j : NNReal) : ℝ) = Sq := by
    rw [NNReal.coe_sum, hSq]
    exact Finset.sum_congr rfl fun j _ => hcval j
  have hεnn : 0 ≤ Ω * Real.sqrt Sq := by positivity
  have hmain := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hXindep hsubG hεnn
  rw [hcsum] at hmain
  have hexpeq : Real.exp (-(Ω * Real.sqrt Sq) ^ 2 / (2 * Sq)) = Real.exp (-(Ω ^ 2 / 2)) := by
    congr 1
    have hs : Real.sqrt Sq ^ 2 = Sq := Real.sq_sqrt hSqnn
    field_simp
    nlinarith [hs]
  rw [hexpeq] at hmain
  refine le_trans (measureReal_mono ?_) hmain
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact hω.le
