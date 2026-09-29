-- Prove2me | solution 1 for ThreeOpSplitting.Accel.prop_3_1_part2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:33:38.009756+00:00
-- url     : https://prove2.me/submissions/6f7393fa-cf8f-4d97-a598-8864cd693f56

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Accel_Algorithm3
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open InnerProductSpace Filter Topology


namespace ThreeOpSplitting.Accel

lemma norm_add_smul_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p q : H) (g : ℝ) :
    ‖p + g • q‖ ^ 2 = ‖p‖ ^ 2 + 2 * g * ⟪p, q⟫_ℝ + g ^ 2 * ‖q‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma norm_sub_smul_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p q : H) (g : ℝ) :
    ‖p - g • q‖ ^ 2 = ‖p‖ ^ 2 - 2 * g * ⟪p, q⟫_ℝ + g ^ 2 * ‖q‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The key two-step inequality, in terms of the relevant points. -/
lemma core_part2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H → Set H) (C : H → H) (μB LC g : ℝ) (a y v x u w xs uAs uBs : H)
    (hAm : IsMonotoneOp A) (hBs : IsStronglyMonotoneOp μB B)
    (hCm : IsMonotoneFun C) (hLC : 0 ≤ LC) (hCL : IsLipschitzOp LC C)
    (hg : 0 < g) (hw : w ∈ A a) (hu : u ∈ B x)
    (hgw : g • w = y - g • v - g • C y - a) (hgu : g • u = a + g • v - x)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0) :
    (1 + 2 * g * (μB - g * LC ^ 2 / 2)) * ‖x - xs‖ ^ 2 + g ^ 2 * LC ^ 2 * ‖x - xs‖ ^ 2
        + g ^ 2 * ‖u - uBs‖ ^ 2
      ≤ ‖y - xs‖ ^ 2 + g ^ 2 * LC ^ 2 * ‖y - xs‖ ^ 2 + g ^ 2 * ‖v - uBs‖ ^ 2 := by
  have hBx := hBs x xs u uBs hu huB
  have hAa := hAm a xs w uAs hw huA
  have hCy := hCm y xs
  have hLy := hCL y xs
  have huBs : uBs = -uAs - C xs := by
    rw [eq_comm, ← sub_eq_zero, ← neg_eq_zero, ← hsum]; abel
  have E1 : (x - xs) + g • (u - uBs) = (a - xs) + g • (v - uBs) := by
    rw [smul_sub, hgu, smul_sub]; abel
  have E2 : (y - xs) - g • (C y - C xs) =
      ((a - xs) + g • (v - uBs)) + g • (w - uAs) := by
    rw [smul_sub g w uAs, hgw, huBs]; module
  -- step 1: strong monotonicity of B
  have S1 : (1 + 2 * g * μB) * ‖x - xs‖ ^ 2 + g ^ 2 * ‖u - uBs‖ ^ 2 ≤
      ‖(a - xs) + g • (v - uBs)‖ ^ 2 := by
    rw [← E1, norm_add_smul_sq]
    nlinarith [mul_le_mul_of_nonneg_left hBx (by linarith : (0:ℝ) ≤ 2 * g)]
  -- step 2: monotonicity of A
  set P := (a - xs) + g • (v - uBs) with hP
  set Q := g • (w - uAs) with hQ
  have hPQ : 0 ≤ ⟪a - xs, Q⟫_ℝ := by
    rw [hQ, real_inner_smul_right]; exact mul_nonneg hg.le hAa
  have hVQ : 0 ≤ ‖g • (v - uBs) + Q‖ ^ 2 := sq_nonneg _
  have S2 : ‖P‖ ^ 2 ≤ ‖P + Q‖ ^ 2 + ‖g • (v - uBs)‖ ^ 2 := by
    rw [norm_add_sq_real (g • (v - uBs)) Q] at hVQ
    rw [norm_add_sq_real P Q]
    have : ⟪P, Q⟫_ℝ = ⟪a - xs, Q⟫_ℝ + ⟪g • (v - uBs), Q⟫_ℝ := by rw [hP, inner_add_left]
    nlinarith
  -- step 3: C monotone and Lipschitz
  have S3 : ‖P + Q‖ ^ 2 ≤ ‖y - xs‖ ^ 2 + g ^ 2 * LC ^ 2 * ‖y - xs‖ ^ 2 := by
    rw [← E2, norm_sub_smul_sq]
    have h1 : ‖C y - C xs‖ ^ 2 ≤ LC ^ 2 * ‖y - xs‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hLy 2
    have h2 : 0 ≤ g * ⟪y - xs, C y - C xs⟫_ℝ := mul_nonneg hg.le hCy
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg g)]
  have S4 : ‖g • (v - uBs)‖ ^ 2 = g ^ 2 * ‖v - uBs‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith

theorem prop_3_1_part2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (JA JB : ℝ → H → H)
    (μB LC : ℝ) (γ : ℕ → ℝ) (xA0 xs uAs uBs : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 < μB) (hBs : IsStronglyMonotoneOp μB B)
    (hCm : IsMonotoneFun C) (hLC : 0 ≤ LC) (hCL : IsLipschitzOp LC C)
    (hγ : ∀ j : ℕ, 0 < γ j)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * LC ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).uB - uBs‖ ^ 2
      ≤ ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * LC ^ 2 * ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set g := γ (j + 1) with hgdef
  have hg : 0 < g := hγ (j + 1)
  set s := accelIter JA JB C γ xA0 (j + 1) with hs
  have hxA : s.xA = JA g (s.xB - g • s.uB - g • C s.xB) := by rw [hs]; rfl
  have hxB : (accelIter JA JB C γ xA0 (j + 1 + 1)).xB = JB g (s.xA + g • s.uB) := by
    rw [hs, hgdef]; rfl
  have huB' : (accelIter JA JB C γ xA0 (j + 1 + 1)).uB =
      g⁻¹ • (s.xA + g • s.uB - (accelIter JA JB C γ xA0 (j + 1 + 1)).xB) := by
    rw [hxB, hs, hgdef]; rfl
  set x := (accelIter JA JB C γ xA0 (j + 1 + 1)).xB
  set u := (accelIter JA JB C γ xA0 (j + 1 + 1)).uB
  set w := g⁻¹ • ((s.xB - g • s.uB - g • C s.xB) - s.xA) with hw
  have hwA : w ∈ A s.xA := by
    have := hJA g hg (s.xB - g • s.uB - g • C s.xB)
    rw [← hxA] at this; exact this
  have huBm : u ∈ B x := by
    have := hJB g hg (s.xA + g • s.uB)
    rw [← hxB] at this; rw [huB']; exact this
  have hgw : g • w = s.xB - g • s.uB - g • C s.xB - s.xA := by
    rw [hw, smul_smul, mul_inv_cancel₀ hg.ne', one_smul]
  have hgu : g • u = s.xA + g • s.uB - x := by
    rw [huB', smul_smul, mul_inv_cancel₀ hg.ne', one_smul]
  exact core_part2 A B C μB LC g s.xA s.xB s.uB x u w xs uAs uBs hA.1 hBs hCm hLC hCL hg
    hwA huBm hgw hgu huA huB hsum

end ThreeOpSplitting.Accel

open ThreeOpSplitting.Accel

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (JA JB : ℝ → H → H)
    (μB LC : ℝ) (γ : ℕ → ℝ) (xA0 xs uAs uBs : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 < μB) (hBs : IsStronglyMonotoneOp μB B)
    (hCm : IsMonotoneFun C) (hLC : 0 ≤ LC) (hCL : IsLipschitzOp LC C)
    (hγ : ∀ j : ℕ, 0 < γ j)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2)) * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * LC ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).uB - uBs‖ ^ 2
      ≤ ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * LC ^ 2 * ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 := by
  exact prop_3_1_part2 A B C JA JB μB LC γ xA0 xs uAs uBs hA hB hμB hBs hCm hLC hCL hγ hJA hJB huA huB hsum k hk
