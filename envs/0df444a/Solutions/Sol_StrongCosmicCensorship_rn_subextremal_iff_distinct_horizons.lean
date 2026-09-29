-- Prove2me | solution 1 for StrongCosmicCensorship.rn_subextremal_iff_distinct_horizons
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:35:04.958996+00:00
-- url     : https://prove2.me/submissions/69fe704d-3aa1-4e43-913f-1af6bcaaa196

import Definitions.Def_scc_coordinate_framework

open Set Filter
open scoped Matrix Topology
open StrongCosmicCensorship

theorem W2c_StrongCosmicCensorship_subextremal_iff (M e : ℝ) (hM : 0 < M)
    (he : e ^ 2 ≤ M ^ 2) :
    |e| < M ↔ rnInnerRadius M e < rnOuterRadius M e := by
  unfold rnInnerRadius rnOuterRadius
  rw [show (M - Real.sqrt (M ^ 2 - e ^ 2) < M + Real.sqrt (M ^ 2 - e ^ 2)) ↔
      0 < Real.sqrt (M ^ 2 - e ^ 2) by constructor <;> intro h <;> linarith,
    Real.sqrt_pos, sub_pos, ← sq_abs e]
  exact (sq_lt_sq₀ (abs_nonneg e) hM.le).symm

theorem W2c_StrongCosmicCensorship_horizons (M e : ℝ) (hM : 0 < M) (he : 0 < |e|)
    (hsub : |e| < M) :
    0 < rnInnerRadius M e ∧ rnInnerRadius M e < rnOuterRadius M e ∧
      ∀ r : ℝ, r ≠ 0 →
        (rnLapse M e r = 0 ↔ r = rnInnerRadius M e ∨ r = rnOuterRadius M e) := by
  have he2 : e ^ 2 < M ^ 2 := by
    nlinarith [sq_abs e, abs_nonneg e, mul_pos (sub_pos.2 hsub)
      (add_pos_of_pos_of_nonneg hM (abs_nonneg e))]
  have he0 : 0 < e ^ 2 := by rw [← sq_abs]; positivity
  have hD : 0 < M ^ 2 - e ^ 2 := by linarith
  unfold rnInnerRadius rnOuterRadius
  set s := Real.sqrt (M ^ 2 - e ^ 2) with hsdef
  have hs2 : s ^ 2 = M ^ 2 - e ^ 2 := Real.sq_sqrt hD.le
  have hs0 : 0 < s := Real.sqrt_pos.2 hD
  have hsM : s < M := by nlinarith
  refine ⟨by linarith, by linarith, fun r hr => ?_⟩
  unfold rnLapse
  have hmul : (1 - 2 * M / r + e ^ 2 / r ^ 2) * r ^ 2 = r ^ 2 - 2 * M * r + e ^ 2 := by
    field_simp
    try ring
  constructor
  · intro h
    have h0 : (1 - 2 * M / r + e ^ 2 / r ^ 2) * r ^ 2 = 0 := by rw [h, zero_mul]
    rw [hmul] at h0
    have h1 : (r - (M - s)) * (r - (M + s)) = 0 := by linear_combination h0 - hs2
    rcases mul_eq_zero.1 h1 with h2 | h2
    · left; linarith
    · right; linarith
  · intro h
    have h0 : (1 - 2 * M / r + e ^ 2 / r ^ 2) * r ^ 2 = 0 := by
      rw [hmul]
      rcases h with h | h <;> rw [h] <;> linear_combination hs2
    exact (mul_eq_zero.1 h0).resolve_right (pow_ne_zero 2 hr)

theorem W2c_StrongCosmicCensorship_mink_st : IsSpacetime (univ : Set Coords) minkowski := by
  refine ⟨isOpen_univ, fun a b => ?_, fun x _ => ⟨1, by simp, by simp [minkowski]⟩⟩
  simp only [minkowski]
  exact contDiffOn_const

theorem W2c_StrongCosmicCensorship_chr_mink :
    ∀ a b c : Fin 4, christoffel minkowski a b c = fun _ => 0 := by
  intro a b c
  funext x
  unfold christoffel pd minkowski
  simp

theorem W2c_StrongCosmicCensorship_mink_vac : IsVacuum (univ : Set Coords) minkowski := by
  intro x _ b d
  unfold ricci riemann pd
  simp [W2c_StrongCosmicCensorship_chr_mink]

theorem W2c_StrongCosmicCensorship_schw_st (M : ℝ) (hM : 0 < M) :
    IsSpacetime (schwarzschildExterior M) (schwarzschild M) := by
  have hopen : IsOpen (schwarzschildExterior M) :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const))
  have hr : ∀ x ∈ schwarzschildExterior M, 0 < x 1 := fun x hx => by
    have := hx.1; linarith
  have hf : ∀ x ∈ schwarzschildExterior M, 0 < schwarzschildLapse M (x 1) := by
    intro x hx
    unfold schwarzschildLapse
    have : 2 * M / x 1 < 1 := (div_lt_one (hr x hx)).2 hx.1
    linarith
  have hlap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Coords => schwarzschildLapse M (x 1))
      (schwarzschildExterior M) := by
    unfold schwarzschildLapse
    exact contDiffOn_const.sub (contDiffOn_const.div
      (contDiff_apply ℝ ℝ (1 : Fin 4)).contDiffOn (fun x hx => (hr x hx).ne'))
  refine ⟨hopen, fun a b => ?_, fun x hx => ?_⟩
  · by_cases hab : a = b
    · subst hab
      fin_cases a
      · simp only [schwarzschild, Matrix.diagonal_apply_eq]
        exact hlap.neg
      · simp only [schwarzschild, Matrix.diagonal_apply_eq]
        exact hlap.inv (fun x hx => (hf x hx).ne')
      · simp only [schwarzschild, Matrix.diagonal_apply_eq]
        exact ((contDiff_apply ℝ ℝ (1 : Fin 4)).pow 2).contDiffOn
      · simp only [schwarzschild, Matrix.diagonal_apply_eq]
        exact (((contDiff_apply ℝ ℝ (1 : Fin 4)).pow 2).mul
          ((Real.contDiff_sin.comp (contDiff_apply ℝ ℝ (2 : Fin 4))).pow 2)).contDiffOn
    · simp only [schwarzschild, Matrix.diagonal_apply_ne _ hab]
      exact contDiffOn_const
  · have hfx := hf x hx
    have hrx := hr x hx
    have hsx : 0 < Real.sin (x 2) := Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
    refine ⟨Matrix.diagonal ![Real.sqrt (schwarzschildLapse M (x 1)),
      (Real.sqrt (schwarzschildLapse M (x 1)))⁻¹, x 1, x 1 * Real.sin (x 2)], ?_, ?_⟩
    · have hsq0 := (Real.sqrt_pos.2 hfx).ne'
      rw [Matrix.det_diagonal]
      apply isUnit_iff_ne_zero.2
      rw [Finset.prod_ne_zero_iff]
      intro i _
      fin_cases i <;> simp [hsq0, hrx.ne', hsx.ne']
    · unfold minkowskiMatrix schwarzschild
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      have hsq := Real.sq_sqrt hfx.le
      have hsq0 := (Real.sqrt_pos.2 hfx).ne'
      fin_cases i
      · simp; nlinarith [hsq]
      · simp; field_simp; linarith [hsq]
      · simp; ring
      · simp; ring

theorem solution (M e : ℝ) (hM : 0 < M) (he : e ^ 2 ≤ M ^ 2) :
    |e| < M ↔ rnInnerRadius M e < rnOuterRadius M e := by
  apply W2c_StrongCosmicCensorship_subextremal_iff <;> assumption
