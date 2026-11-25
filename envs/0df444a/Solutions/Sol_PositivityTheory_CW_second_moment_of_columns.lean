-- Prove2me | solution 1 for PositivityTheory.CW.second_moment_of_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:39:48.220243+00:00
-- url     : https://prove2.me/submissions/3a984b25-afdd-4cd7-8410-dd16e9eb9679

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle
import Theorems.Thm_PositivityTheory_CW_SecondMomentAlgebra_alg
import Theorems.Thm_PositivityTheory_CW_SecondMomentAlgebra_reEig
import Theorems.Thm_PositivityTheory_CW_SecondMomentAlgebra_cs
import Theorems.Thm_PositivityTheory_CW_SecondMomentAlgebra_zsum
import Theorems.Thm_PositivityTheory_CW_SecondMomentAlgebra_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
set_option maxHeartbeats 800000
namespace PositivityTheory.CW
theorem _root_.solution : A0 → A1 → FiltrationAdjointStable → CasimirIsRealScalar → A5 → A6 → ColumnOperatorMoments → A8 := by
  intro h0 h1 h1s h3c h5 h6 h8a n ε V _ _ E hM
  obtain ⟨-, -, hZc, hcas⟩ := h0 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3c n ε V E hM
  set m : ℕ := 2 ^ n with hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  have hnm : n ≤ m := Nat.lt_two_pow_self.le
  have h5' := h5 n ε V E hM m hm1 hnm
  choose u hu w hw hdec using fun e : Fin n => h5' e e
  have hadj : ∀ e c d, ∃ w' ∈ U E (2 * m - 2), ∀ x y : V,
      inner ℂ x (w e c d y) = inner ℂ (w' x) y := fun e c d => h1s n ε V E hM _ _ (hw e c d)
  choose w' hw' hadj using hadj
  have bu : ∀ e, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖u e v‖ ≤ C * √(1 + μ) ^ (2 * m - 1) * ‖v‖ := fun e => h6 n ε V E hM _ _ (hu e)
  choose Cu hCu0 hCu using bu
  have bw : ∀ e c d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖w' e c d v‖ ≤ C * √(1 + μ) ^ (2 * m - 2) * ‖v‖ := fun e c d => h6 n ε V E hM _ _ (hw' e c d)
  choose Cw hCw0 hCw using bw
  set C1 : ℝ := ∑ e, Cu e with hC1def
  set C2 : ℝ := ∑ e, ∑ c, ∑ d, Cw e c d + 1 with hC2def
  have hC1e : ∀ e, Cu e ≤ C1 := fun e =>
    Finset.single_le_sum (f := Cu) (fun i _ => hCu0 i) (Finset.mem_univ e)
  have hC2e : ∀ e c d, Cw e c d ≤ C2 := by
    intro e c d
    have a1 : Cw e c d ≤ ∑ d', Cw e c d' :=
      Finset.single_le_sum (f := fun d' => Cw e c d') (fun i _ => hCw0 e c i) (Finset.mem_univ d)
    have a2 : ∑ d', Cw e c d' ≤ ∑ c', ∑ d', Cw e c' d' :=
      Finset.single_le_sum (f := fun c' => ∑ d', Cw e c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => hCw0 e i j)) (Finset.mem_univ c)
    have a3 : ∑ c', ∑ d', Cw e c' d' ≤ ∑ e', ∑ c', ∑ d', Cw e' c' d' :=
      Finset.single_le_sum (f := fun e' => ∑ c', ∑ d', Cw e' c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
        (Finset.mem_univ e)
    linarith
  have hC2 : 0 < C2 := by
    have : 0 ≤ ∑ e, ∑ c, ∑ d, Cw e c d :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
    linarith
  set N : ℝ := (2 * (n:ℝ)) ^ m with hNdef
  refine ⟨1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1), max (max 1 (|κ| + 1)) ((2 * C1 * N) ^ 2),
    by positivity, ?_⟩
  intro μ v hμ hv
  have hμ1 : 1 ≤ μ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hμ
  have hμκ : |κ| + 1 ≤ μ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hμ
  have hμC : (2 * C1 * N) ^ 2 ≤ μ := le_trans (le_max_right _ _) hμ
  by_cases hv0 : v = 0
  · subst hv0
    simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set v1 : V := ((‖v‖ : ℂ)⁻¹) • v with hv1def
  have hv1n : ‖v1‖ = 1 := by
    rw [hv1def, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hv1E : Eig ε E μ v1 := by
    have hv' : casimirK ε E v = (μ : ℂ) • v := hv
    show casimirK ε E (((‖v‖ : ℂ)⁻¹) • v) = (μ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v)
    rw [map_smul, hv', smul_comm]
  rw [SecondMomentAlgebra.scale ε E v hv0]
  suffices hS : 1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1) * (1 + μ) ^ 2 ≤
      ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v1‖ ^ 2 by
    have := mul_le_mul_of_nonneg_left hS (sq_nonneg ‖v‖)
    linarith
  have hX : ∑ a, ∑ b, ‖E a b v1‖ ^ 2 = 2 * μ - κ := by
    rw [(hcas κ hκ v1).1, show casimirK ε E v1 = (μ : ℂ) • v1 from hv1E, SecondMomentAlgebra.reEig, hv1n]
    ring
  have hpos : 0 < 2 * μ - κ := by linarith [le_abs_self κ]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hX
    simp at hX
    linarith
  obtain ⟨e0, -⟩ := hne
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Fin.pos e0)
  have hnr : (n:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN : 0 < N := by positivity
  obtain ⟨e, -, he⟩ := exists_le_of_sum_le (s := Finset.univ) ⟨e0, Finset.mem_univ _⟩
    (f := fun _ => (2 * μ - κ) / n) (g := fun e => ∑ a, ‖E a e v1‖ ^ 2) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (n:ℝ) * ((2 * μ - κ) / n) = 2 * μ - κ := by field_simp
      rw [this, ← hX, Finset.sum_comm])
  have h8 := h8a n ε V E hM v1 hv1n e n
  rw [hdec e] at h8
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, inner_add_right, inner_sum,
    Complex.add_re, Complex.re_sum] at h8
  have hs : √(1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
  have b1 : (inner ℂ v1 (u e v1)).re ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
    have r := re_inner_le_norm (𝕜 := ℂ) v1 (u e v1)
    have r2 : ‖u e v1‖ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
      simpa [hv1n] using hCu e μ v1 (by linarith) hv1E
    rw [hv1n, one_mul] at r
    exact le_trans r r2
  have b2 : ∀ c d, (inner ℂ v1 (w e c d (Z ε E c d v1))).re ≤
      C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ := by
    intro c d
    rw [hadj e c d]
    have r := re_inner_le_norm (𝕜 := ℂ) (w' e c d v1) (Z ε E c d v1)
    have r2 : ‖w' e c d v1‖ ≤ C2 * √(1 + μ) ^ (2 * m - 2) := by
      have := hCw e c d μ v1 (by linarith) hv1E
      rw [hv1n, mul_one] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (hC2e e c d) (by positivity))
    exact le_trans r (mul_le_mul_of_nonneg_right r2 (norm_nonneg _))
  have hsum : ∑ c, ∑ d, ‖Z ε E c d v1‖ ≤ √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt (SecondMomentAlgebra.cs (fun c d => ‖Z ε E c d v1‖)))
  set T := √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) with hTdef
  have hXe : √(1 + μ) ^ 2 / (2 * n) ≤ ∑ a, ‖E a e v1‖ ^ 2 := by
    rw [hs]
    calc (1 + μ) / (2 * n) ≤ (2 * μ - κ) / n := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [le_abs_self κ]
      _ ≤ _ := he
  have hmain : (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤
      C1 * √(1 + μ) ^ (2 * m - 1) + C2 * √(1 + μ) ^ (2 * m - 2) * T := by
    calc (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤ (∑ a, ‖E a e v1‖ ^ 2) ^ m :=
          pow_le_pow_left₀ (by positivity) hXe m
      _ ≤ _ := h8
      _ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) + ∑ c, ∑ d, C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ :=
          add_le_add b1 (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => b2 c d)
      _ ≤ _ := by
          simp_rw [← Finset.mul_sum]
          exact add_le_add (mul_le_mul_of_nonneg_right (hC1e e) (by positivity))
            (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hs1 : 1 ≤ √(1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have hs2 : 2 * C1 * N ≤ √(1 + μ) := by
    refine le_trans (le_abs_self _) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have key := SecondMomentAlgebra.alg n m C1 C2 (√(1 + μ)) T hn1 hm1 hC2 hs1 hs2 hmain
  rw [hs] at key
  have hS'0 : 0 ≤ ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by positivity
  have hq : (1 / (2 * N * C2) * (1 + μ)) ^ 2 ≤ (n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) key 2
    rwa [hTdef, Real.sq_sqrt (by positivity)] at this
  have hq' : (1 + μ) ^ 2 ≤ (2 * N * C2) ^ 2 * ((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) := by
    have e3 : (1 + μ) ^ 2 = (2 * N * C2) ^ 2 * (1 / (2 * N * C2) * (1 + μ)) ^ 2 := by
      field_simp
    rw [e3]
    exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
  rw [← SecondMomentAlgebra.zsum ε E hZc v1]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hS'0 (sq_nonneg (2 * N * C2))]
end PositivityTheory.CW
