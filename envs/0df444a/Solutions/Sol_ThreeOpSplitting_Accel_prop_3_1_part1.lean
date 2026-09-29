-- Prove2me | solution 1 for ThreeOpSplitting.Accel.prop_3_1_part1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:36:19.308925+00:00
-- url     : https://prove2.me/submissions/15423449-7e3b-46fc-9b8c-02bf49aedf76

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

lemma polar3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a b c : H) :
    2 * ⟪a - b, c - a⟫_ℝ = ‖b - c‖ ^ 2 - ‖a - b‖ ^ 2 - ‖a - c‖ ^ 2 := by
  rw [show b - c = (b - a) + (a - c) by abel, norm_add_sq_real,
    show a - b = -(b - a) by abel, show c - a = -(a - c) by abel, inner_neg_left,
    inner_neg_right, norm_neg]
  ring

lemma core_part1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H → Set H) (C : H → H) (μB μC β η g : ℝ) (a y v x u w xs uAs uBs : H)
    (hAm : IsMonotoneOp A) (hBs : IsStronglyMonotoneOp μB B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hCs : IsStronglyMonotoneFun μC C)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hg : 0 < g) (hw : w ∈ A a) (hu : u ∈ B x)
    (hgw : g • w = y - g • v - g • C y - a) (hgu : g • u = a + g • v - x)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0) :
    (1 + 2 * g * μB) * ‖x - xs‖ ^ 2 + g ^ 2 * ‖u - uBs‖ ^ 2
        + (1 - g / (2 * (1 - η) * β)) * ‖a - y‖ ^ 2
      ≤ (1 - 2 * g * μC * η) * ‖y - xs‖ ^ 2 + g ^ 2 * ‖v - uBs‖ ^ 2 := by
  have hBx := hBs x xs u uBs hu huB
  have hAa := hAm a xs w uAs hw huA
  have hCc := hC y xs
  have hCsy := hCs y xs
  have huBs : uBs = -uAs - C xs := by
    rw [eq_comm, ← sub_eq_zero, ← neg_eq_zero, ← hsum]; abel
  have E1 : (x - xs) + g • (u - uBs) = (a - xs) + g • (v - uBs) := by
    rw [smul_sub, hgu, smul_sub]; abel
  have E2 : g • (v - uBs) = (y - a) - g • (C y - C xs) - g • (w - uAs) := by
    rw [smul_sub g w uAs, hgw, huBs]; module
  -- step 1: strong monotonicity of B
  have S1 : (1 + 2 * g * μB) * ‖x - xs‖ ^ 2 + g ^ 2 * ‖u - uBs‖ ^ 2 ≤
      ‖(a - xs) + g • (v - uBs)‖ ^ 2 := by
    rw [← E1, norm_add_smul_sq]
    nlinarith [mul_le_mul_of_nonneg_left hBx (by linarith : (0:ℝ) ≤ 2 * g)]
  -- expand ‖P‖²
  have S2 : ‖(a - xs) + g • (v - uBs)‖ ^ 2 = ‖a - xs‖ ^ 2 + 2 * g * ⟪a - xs, v - uBs⟫_ℝ
      + g ^ 2 * ‖v - uBs‖ ^ 2 := norm_add_smul_sq _ _ _
  -- the cross term
  have S3 : g * ⟪a - xs, v - uBs⟫_ℝ = ⟪a - xs, y - a⟫_ℝ - g * ⟪a - xs, C y - C xs⟫_ℝ
      - g * ⟪a - xs, w - uAs⟫_ℝ := by
    rw [← real_inner_smul_right, E2, inner_sub_right, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right]
  have P3 := polar3 a xs y
  -- splitting ⟪a - xs, D⟫ = ⟪y - xs, D⟫ + ⟪a - y, D⟫
  set D := C y - C xs with hD
  have S4 : ⟪a - xs, D⟫_ℝ = ⟪y - xs, D⟫_ℝ + ⟪a - y, D⟫_ℝ := by
    rw [← inner_add_left]; congr 1; abel
  have hDy : ⟪D, y - xs⟫_ℝ = ⟪y - xs, D⟫_ℝ := real_inner_comm _ _
  -- AM-GM with c = 2(1-η)β
  set c := 2 * (1 - η) * β with hc
  have hcpos : 0 < c := by rw [hc]; have : 0 < 1 - η := by linarith
                           positivity
  have hAM0 : 0 ≤ ‖(a - y) + c • D‖ ^ 2 := sq_nonneg _
  rw [norm_add_smul_sq] at hAM0
  have hAM : -2 * g * ⟪a - y, D⟫_ℝ ≤ g / c * ‖a - y‖ ^ 2 + g * c * ‖D‖ ^ 2 := by
    have h1 := mul_nonneg (div_nonneg hg.le hcpos.le) hAM0
    have e : g / c * (‖a - y‖ ^ 2 + 2 * c * ⟪a - y, D⟫_ℝ + c ^ 2 * ‖D‖ ^ 2) =
        g / c * ‖a - y‖ ^ 2 + 2 * g * ⟪a - y, D⟫_ℝ + g * c * ‖D‖ ^ 2 := by
      field_simp
    linarith
  -- lower bound on ⟪y - xs, D⟫ via η-split
  have hsplit : η * μC * ‖y - xs‖ ^ 2 + (1 - η) * β * ‖D‖ ^ 2 ≤ ⟪y - xs, D⟫_ℝ := by
    have h1 := mul_le_mul_of_nonneg_left hCsy hη0.le
    have h2 := mul_le_mul_of_nonneg_left hCc (by linarith : (0:ℝ) ≤ 1 - η)
    rw [hDy] at h2
    nlinarith
  have hgA : 0 ≤ g * ⟪a - xs, w - uAs⟫_ℝ := mul_nonneg hg.le hAa
  have hgs := mul_le_mul_of_nonneg_left hsplit (by linarith : (0:ℝ) ≤ 2 * g)
  have hcc : g * c * ‖D‖ ^ 2 = 2 * g * ((1 - η) * β * ‖D‖ ^ 2) := by rw [hc]; ring
  rw [S2] at S1
  have n1 : ‖xs - y‖ ^ 2 = ‖y - xs‖ ^ 2 := by rw [norm_sub_rev]
  have S4' : g * ⟪a - xs, D⟫_ℝ = g * ⟪y - xs, D⟫_ℝ + g * ⟪a - y, D⟫_ℝ := by rw [S4]; ring
  linarith

theorem prop_3_1_part1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (JA JB : ℝ → H → H)
    (μB μC β η : ℝ) (γ : ℕ → ℝ) (xA0 xs uAs uBs : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 ≤ μB) (hBs : IsStronglyMonotoneOp μB B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hμC : 0 < μC) (hCs : IsStronglyMonotoneFun μC C)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hγ : ∀ j : ℕ, 0 < γ j ∧ γ j < 2 * (1 - η) * β)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + 2 * γ k * μB) * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).uB - uBs‖ ^ 2
        + (1 - γ k / (2 * (1 - η) * β))
          * ‖(accelIter JA JB C γ xA0 k).xA - (accelIter JA JB C γ xA0 k).xB‖ ^ 2
      ≤ (1 - 2 * γ k * μC * η) * ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set g := γ (j + 1) with hgdef
  have hg : 0 < g := (hγ (j + 1)).1
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
  exact core_part1 A B C μB μC β η g s.xA s.xB s.uB x u w xs uAs uBs hA.1 hBs hβ hC hCs hη0 hη1
    hg hwA huBm hgw hgu huA huB hsum

end ThreeOpSplitting.Accel

open ThreeOpSplitting.Accel

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (JA JB : ℝ → H → H)
    (μB μC β η : ℝ) (γ : ℕ → ℝ) (xA0 xs uAs uBs : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hμB : 0 ≤ μB) (hBs : IsStronglyMonotoneOp μB B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hμC : 0 < μC) (hCs : IsStronglyMonotoneFun μC C)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hγ : ∀ j : ℕ, 0 < γ j ∧ γ j < 2 * (1 - η) * β)
    (hJA : IsResolventFamily A JA) (hJB : IsResolventFamily B JB)
    (huA : uAs ∈ A xs) (huB : uBs ∈ B xs) (hsum : uAs + uBs + C xs = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (1 + 2 * γ k * μB) * ‖(accelIter JA JB C γ xA0 (k + 1)).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 (k + 1)).uB - uBs‖ ^ 2
        + (1 - γ k / (2 * (1 - η) * β))
          * ‖(accelIter JA JB C γ xA0 k).xA - (accelIter JA JB C γ xA0 k).xB‖ ^ 2
      ≤ (1 - 2 * γ k * μC * η) * ‖(accelIter JA JB C γ xA0 k).xB - xs‖ ^ 2
        + γ k ^ 2 * ‖(accelIter JA JB C γ xA0 k).uB - uBs‖ ^ 2 := by
  exact prop_3_1_part1 A B C JA JB μB μC β η γ xA0 xs uAs uBs hA hB hμB hBs hβ hC hμC hCs hη0 hη1 hγ hJA hJB huA huB hsum k hk
