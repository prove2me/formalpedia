-- Prove2me | solution 1 for QAlgorithms.Nannicini.expPoly_approx
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:59:23.739743+00:00
-- url     : https://prove2.me/submissions/c57f6500-88f2-448d-aa7c-ba1f173ff5f5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false

open Polynomial

private noncomputable def hCubicPoly : ℝ[X] :=
  C 3 * X ^ 2 - C 2 * X ^ 3

private noncomputable def iterHPoly : ℕ → ℝ[X] → ℝ[X]
  | 0, P => P
  | k + 1, P => hCubicPoly.comp (iterHPoly k P)

private noncomputable def hCubic (u : ℝ) : ℝ :=
  3 * u ^ 2 - 2 * u ^ 3

private lemma eval_hCubicPoly (u : ℝ) : hCubicPoly.eval u = hCubic u := by
  simp [hCubicPoly, hCubic]

private lemma eval_iterHPoly (k : ℕ) (P : ℝ[X]) (x : ℝ) :
    (iterHPoly k P).eval x = hCubic^[k] (P.eval x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterHPoly, eval_comp, eval_hCubicPoly, Function.iterate_succ_apply', ih]

private lemma natDegree_hCubicPoly_le : hCubicPoly.natDegree ≤ 3 := by
  dsimp [hCubicPoly]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans natDegree_mul_le ?_; simp
  · refine le_trans natDegree_mul_le ?_; simp

private lemma natDegree_iterHPoly_le (k : ℕ) (P : ℝ[X]) :
    (iterHPoly k P).natDegree ≤ 3 ^ k * P.natDegree := by
  induction k with
  | zero => simp [iterHPoly]
  | succ k ih =>
    rw [iterHPoly]
    calc (hCubicPoly.comp (iterHPoly k P)).natDegree
      _ ≤ hCubicPoly.natDegree * (iterHPoly k P).natDegree := natDegree_comp_le
      _ ≤ 3 * (3 ^ k * P.natDegree) :=
          Nat.mul_le_mul natDegree_hCubicPoly_le ih
      _ = 3 ^ (k + 1) * P.natDegree := by rw [pow_succ', mul_assoc]

private lemma hCubic_mem_Icc {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ hCubic u ∧ hCubic u ≤ 1 := by
  constructor
  · have : hCubic u = u ^ 2 * (3 - 2 * u) := by dsimp [hCubic]; ring
    rw [this]; nlinarith
  · have : 1 - hCubic u = (1 - u) ^ 2 * (1 + 2 * u) := by dsimp [hCubic]; ring
    linarith [mul_nonneg (sq_nonneg (1 - u)) (by linarith : (0 : ℝ) ≤ 1 + 2 * u)]

private lemma iter_hCubic_mem_Icc (k : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ hCubic^[k] u ∧ hCubic^[k] u ≤ 1 := by
  induction k with
  | zero => exact ⟨hu0, hu1⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hCubic_mem_Icc ih.1 ih.2

private lemma hCubic_symm (u : ℝ) : hCubic (1 - u) = 1 - hCubic u := by
  dsimp [hCubic]; ring

private lemma iter_hCubic_symm (k : ℕ) (u : ℝ) :
    hCubic^[k] (1 - u) = 1 - hCubic^[k] u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hCubic_symm]

private lemma hCubic_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    hCubic a ≤ hCubic b := by
  have hid : hCubic b - hCubic a =
      (b - a) * (a * (3 - 2 * a - b) + b * (3 - a - 2 * b)) := by
    dsimp [hCubic]; ring
  have h1 : 0 ≤ a * (3 - 2 * a - b) + b * (3 - a - 2 * b) := by nlinarith
  linarith [mul_nonneg (sub_nonneg.mpr hab) h1]

private lemma hCubic_amp_step {u γ : ℝ} (hu0 : 0 ≤ u) (huγ : u ≤ 1 / 2 - γ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 3) :
    hCubic u ≤ 1 / 2 - min (1 / 3) ((5 / 4) * γ) := by
  have h1 : hCubic u ≤ hCubic (1 / 2 - γ) :=
    hCubic_mono hu0 huγ (by linarith)
  have h2 : hCubic (1 / 2 - γ) = 1 / 2 - γ * (3 / 2 - 2 * γ ^ 2) := by
    dsimp [hCubic]; ring
  have h3 : (5 / 4) * γ ≤ γ * (3 / 2 - 2 * γ ^ 2) := by nlinarith
  have h4 : min (1 / 3) ((5 / 4) * γ) ≤ (5 / 4) * γ := min_le_right _ _
  linarith

private lemma iter_hCubic_phase1 (k : ℕ) {u γ : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hγ0 : 0 ≤ γ) (huγ : u ≤ 1 / 2 - min (1 / 3) γ) :
    hCubic^[k] u ≤ 1 / 2 - min (1 / 3) ((5 / 4) ^ k * γ) := by
  induction k with
  | zero => simpa using huγ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set γk := min (1 / 3) ((5 / 4) ^ k * γ)
    have hγk0 : 0 ≤ γk := le_min (by norm_num) (by positivity)
    have hγk1 : γk ≤ 1 / 3 := min_le_left _ _
    have hstep := hCubic_amp_step (iter_hCubic_mem_Icc k hu0 hu1).1 ih hγk0 hγk1
    have hmin_eq : min (1 / 3) ((5 / 4) * γk) = min (1 / 3) ((5 / 4) ^ (k + 1) * γ) := by
      dsimp [γk]
      rcases le_total (1 / 3 : ℝ) ((5 / 4) ^ k * γ) with h | h
      · rw [min_eq_left h]
        have h' : (1 / 3 : ℝ) ≤ (5 / 4) ^ (k + 1) * γ := by
          rw [pow_succ']; linarith
        rw [min_eq_left h', min_eq_left (by norm_num : (1 / 3 : ℝ) ≤ (5 / 4) * (1 / 3))]
      · rw [min_eq_right h, pow_succ', mul_assoc]
    rwa [← hmin_eq]

private lemma iter_hCubic_phase2 (k : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 6) :
    hCubic^[k] u ≤ (1 / 3) * (1 / 2) ^ (2 ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero, pow_one, Function.iterate_zero_apply]
    linarith
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set v := hCubic^[k] u
    have hv0 : 0 ≤ v := (iter_hCubic_mem_Icc k hu0 (by linarith)).1
    have h1 : hCubic v ≤ 3 * v ^ 2 := by
      have : 3 * v ^ 2 - hCubic v = 2 * v ^ 3 := by dsimp [hCubic]; ring
      have : 0 ≤ 2 * v ^ 3 := by positivity
      linarith
    have h2 : v ^ 2 ≤ ((1 / 3) * (1 / 2) ^ (2 ^ k)) ^ 2 :=
      pow_le_pow_left₀ hv0 ih 2
    calc hCubic v
      _ ≤ 3 * v ^ 2 := h1
      _ ≤ 3 * ((1 / 3) * (1 / 2) ^ (2 ^ k)) ^ 2 := by linarith
      _ = (1 / 3) * ((1 / 2) ^ (2 ^ k)) ^ 2 := by ring
      _ = (1 / 3) * (1 / 2) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

private lemma iter_hCubic_stopband (s1 s2 : ℕ) {u γ : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hγ0 : 0 ≤ γ) (huγ : u ≤ 1 / 2 - min (1 / 3) γ)
    (hs1 : 1 / 3 ≤ (5 / 4) ^ s1 * γ) :
    hCubic^[s1 + s2] u ≤ (1 / 3) * (1 / 2) ^ (2 ^ s2) := by
  rw [add_comm s1 s2, Function.iterate_add_apply]
  have hp1 := iter_hCubic_phase1 s1 hu0 hu1 hγ0 huγ
  rw [min_eq_left hs1] at hp1
  have hv0 : 0 ≤ hCubic^[s1] u := (iter_hCubic_mem_Icc s1 hu0 hu1).1
  have hv1 : hCubic^[s1] u ≤ 1 / 6 := by linarith
  exact iter_hCubic_phase2 s2 hv0 hv1

private lemma chebT_bound_stopband (l : ℕ) {u : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 1) :
    |(Polynomial.Chebyshev.T ℝ l).eval u| ≤ 1 := by
  set θ := Real.arccos u
  have hcos : Real.cos θ = u := Real.cos_arccos hu1 hu2
  rw [← hcos, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

private lemma chebT_passband_ind (l : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hlδ : (l : ℝ) ^ 2 * δ ≤ 1 / 2) :
    ∀ k ≤ l,
      1 + (k : ℝ) ^ 2 * δ ≤ (Polynomial.Chebyshev.T ℝ k).eval (1 + δ) ∧
      (Polynomial.Chebyshev.T ℝ k).eval (1 + δ) ≤ 1 + 2 * (k : ℝ) ^ 2 * δ ∧
      (2 * (k : ℝ) + 1) * δ ≤
        (Polynomial.Chebyshev.T ℝ ((k : ℤ) + 1)).eval (1 + δ) -
          (Polynomial.Chebyshev.T ℝ k).eval (1 + δ) ∧
      (Polynomial.Chebyshev.T ℝ ((k : ℤ) + 1)).eval (1 + δ) -
          (Polynomial.Chebyshev.T ℝ k).eval (1 + δ) ≤
        2 * (2 * (k : ℝ) + 1) * δ := by
  intro k hk
  induction k with
  | zero =>
    simp only [CharP.cast_eq_zero, Polynomial.Chebyshev.T_zero, eval_one, zero_add,
      Polynomial.Chebyshev.T_one, eval_X]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  | succ k ih =>
    have hk_le : k ≤ l := Nat.le_of_succ_le hk
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih hk_le
    set Tk := (Polynomial.Chebyshev.T ℝ k).eval (1 + δ)
    set Tk1 := (Polynomial.Chebyshev.T ℝ ((k : ℤ) + 1)).eval (1 + δ)
    set Tk2 := (Polynomial.Chebyshev.T ℝ ((k : ℤ) + 2)).eval (1 + δ)
    have hrec : Tk2 - Tk1 = (Tk1 - Tk) + 2 * δ * Tk1 := by
      dsimp [Tk, Tk1, Tk2]
      rw [Polynomial.Chebyshev.T_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
      ring
    have hcast2 : ((k + 1 : ℕ) : ℤ) + 1 = (k : ℤ) + 2 := by push_cast; ring
    have hcast1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    have hcastR : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
    rw [hcast2, hcast1, hcastR]
    change 1 + ((k : ℝ) + 1) ^ 2 * δ ≤ Tk1 ∧
      Tk1 ≤ 1 + 2 * ((k : ℝ) + 1) ^ 2 * δ ∧
      (2 * ((k : ℝ) + 1) + 1) * δ ≤ Tk2 - Tk1 ∧
      Tk2 - Tk1 ≤ 2 * (2 * ((k : ℝ) + 1) + 1) * δ
    have hTk1_lo : 1 + ((k : ℝ) + 1) ^ 2 * δ ≤ Tk1 := by nlinarith
    have hTk1_hi : Tk1 ≤ 1 + 2 * ((k : ℝ) + 1) ^ 2 * δ := by nlinarith
    have hk1_le : ((k : ℝ) + 1) ^ 2 * δ ≤ 1 / 2 := by
      have hkle : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hk
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ (l : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hTk1_ge1 : 1 ≤ Tk1 := by nlinarith
    have hTk1_le2 : Tk1 ≤ 2 := by linarith
    refine ⟨hTk1_lo, hTk1_hi, ?_, ?_⟩
    · rw [hrec]; nlinarith
    · rw [hrec]; nlinarith

private lemma chebT_passband (l : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hlδ : (l : ℝ) ^ 2 * δ ≤ 1 / 5) :
    1 + (l : ℝ) ^ 2 * δ ≤ (Polynomial.Chebyshev.T ℝ l).eval (1 + δ) ∧
    (Polynomial.Chebyshev.T ℝ l).eval (1 + δ) ≤ 7 / 5 := by
  have h := chebT_passband_ind l hδ0 (by linarith) l (le_refl l)
  refine ⟨h.1, ?_⟩
  linarith [h.2.1]

private noncomputable def uQuadPoly (x0 r2 : ℝ) : ℝ[X] :=
  C (1 + 2 * (r2 ^ 2 - x0 ^ 2) / (9 - r2 ^ 2)) +
    C (4 * x0 / (9 - r2 ^ 2)) * X +
    C (-2 / (9 - r2 ^ 2)) * X ^ 2

private lemma eval_uQuadPoly (x0 r2 x : ℝ) :
    (uQuadPoly x0 r2).eval x = 1 + 2 * (r2 ^ 2 - (x - x0) ^ 2) / (9 - r2 ^ 2) := by
  dsimp [uQuadPoly]
  simp only [eval_add, eval_C, eval_mul, eval_X, eval_pow]
  ring

private lemma natDegree_uQuadPoly_le (x0 r2 : ℝ) :
    (uQuadPoly x0 r2).natDegree ≤ 2 := by
  dsimp [uQuadPoly]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · refine (natDegree_C_mul_le _ _).trans ?_; simp
  · refine (natDegree_C_mul_le _ _).trans ?_; simp

private noncomputable def u0BumpPoly (l : ℕ) (x0 r2 η : ℝ) : ℝ[X] :=
  C (1 / (2 + η)) * ((Polynomial.Chebyshev.T ℝ l).comp (uQuadPoly x0 r2)) ^ 2

private lemma eval_u0BumpPoly (l : ℕ) (x0 r2 η x : ℝ) :
    (u0BumpPoly l x0 r2 η).eval x =
      ((Polynomial.Chebyshev.T ℝ l).eval ((uQuadPoly x0 r2).eval x)) ^ 2 / (2 + η) := by
  dsimp [u0BumpPoly]
  simp only [eval_mul, eval_C, eval_pow, eval_comp]
  ring

private lemma natDegree_u0BumpPoly_le (l : ℕ) (x0 r2 η : ℝ) :
    (u0BumpPoly l x0 r2 η).natDegree ≤ 4 * l := by
  dsimp [u0BumpPoly]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_pow_le).trans ?_
  have hcomp : ((Polynomial.Chebyshev.T ℝ l).comp (uQuadPoly x0 r2)).natDegree ≤ l * 2 := by
    refine natDegree_comp_le.trans ?_
    rw [Polynomial.Chebyshev.natDegree_T]
    exact Nat.mul_le_mul_left l (natDegree_uQuadPoly_le x0 r2)
  omega

private lemma u0Bump_properties (l : ℕ) {x0 r1 r2 η : ℝ}
    (hx0_lo : -1 / 2 ≤ x0) (hx0_hi : x0 ≤ 0)
    (hr1_pos : 0 < r1) (hr12 : r1 ≤ r2) (hr2_hi : r2 ≤ 5 / 8)
    (hl_δ0 : (l : ℝ) ^ 2 * (2 * r2 ^ 2 / (9 - r2 ^ 2)) ≤ 1 / 5)
    (hη_eq : η = (l : ℝ) ^ 2 * (2 * (r2 ^ 2 - r1 ^ 2) / (9 - r2 ^ 2)))
    (hη_pos : 0 < η) (hη_hi : η ≤ 1 / 5) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (u0BumpPoly l x0 r2 η).eval x ∧ (u0BumpPoly l x0 r2 η).eval x ≤ 1) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, r2 ≤ |x - x0| →
      (u0BumpPoly l x0 r2 η).eval x ≤ 1 / 2 - η / 5) ∧
    (∀ x : ℝ, |x - x0| ≤ r1 →
      1 / 2 + η / 5 ≤ (u0BumpPoly l x0 r2 η).eval x) := by
  have h9 : 8 ≤ 9 - r2 ^ 2 := by nlinarith
  have h9_pos : 0 < 9 - r2 ^ 2 := by linarith
  have h2η_pos : 0 < 2 + η := by linarith
  have h_stop : ∀ x ∈ Set.Icc (-1 : ℝ) 1, r2 ≤ |x - x0| →
      ((Polynomial.Chebyshev.T ℝ l).eval ((uQuadPoly x0 r2).eval x)) ^ 2 ≤ 1 := by
    intro x hx hrx
    have hx1 : -1 ≤ x := hx.1
    have hx2 : x ≤ 1 := hx.2
    have hsq_lo : r2 ^ 2 ≤ (x - x0) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hrx 2
      rwa [sq_abs] at this
    have hsq_hi : (x - x0) ^ 2 ≤ 9 := by nlinarith
    have hu_hi : (uQuadPoly x0 r2).eval x ≤ 1 := by
      rw [eval_uQuadPoly]
      have : 2 * (r2 ^ 2 - (x - x0) ^ 2) / (9 - r2 ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) h9_pos.le
      linarith
    have hu_lo : -1 ≤ (uQuadPoly x0 r2).eval x := by
      rw [eval_uQuadPoly]
      have : -2 ≤ 2 * (r2 ^ 2 - (x - x0) ^ 2) / (9 - r2 ^ 2) := by
        rw [le_div_iff₀ h9_pos]
        nlinarith
      linarith
    have habs := chebT_bound_stopband l hu_lo hu_hi
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rwa [sq_abs, one_pow] at hsq
  have h_pass_upper : ∀ x : ℝ, |x - x0| ≤ r2 →
      ((Polynomial.Chebyshev.T ℝ l).eval ((uQuadPoly x0 r2).eval x)) ^ 2 ≤ 2 := by
    intro x hrx
    have hsq_hi : (x - x0) ^ 2 ≤ r2 ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hrx 2
      rwa [sq_abs] at this
    set δ := 2 * (r2 ^ 2 - (x - x0) ^ 2) / (9 - r2 ^ 2)
    have hδ0 : 0 ≤ δ := div_nonneg (by linarith) h9_pos.le
    have hδ_le : δ ≤ 2 * r2 ^ 2 / (9 - r2 ^ 2) :=
      div_le_div_of_nonneg_right (by nlinarith) h9_pos.le
    have hlδ : (l : ℝ) ^ 2 * δ ≤ 1 / 5 :=
      (mul_le_mul_of_nonneg_left hδ_le (sq_nonneg _)).trans hl_δ0
    have heval : (uQuadPoly x0 r2).eval x = 1 + δ := eval_uQuadPoly x0 r2 x
    rw [heval]
    obtain ⟨hlo, hhi⟩ := chebT_passband l hδ0 hlδ
    have h_l2δ : 0 ≤ (l : ℝ) ^ 2 * δ := mul_nonneg (sq_nonneg _) hδ0
    have hpos : 0 ≤ (Polynomial.Chebyshev.T ℝ l).eval (1 + δ) := by linarith
    have hsq := pow_le_pow_left₀ hpos hhi 2
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [eval_u0BumpPoly]
    refine ⟨div_nonneg (sq_nonneg _) h2η_pos.le, ?_⟩
    rw [div_le_one h2η_pos]
    rcases le_or_gt r2 |x - x0| with h | h
    · have := h_stop x hx h; linarith
    · have := h_pass_upper x h.le; linarith
  · intro x hx hrx
    rw [eval_u0BumpPoly]
    have h1 := h_stop x hx hrx
    rw [div_le_iff₀ h2η_pos]
    nlinarith
  · intro x hrx
    rw [eval_u0BumpPoly]
    have hsq_hi : (x - x0) ^ 2 ≤ r1 ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hrx 2
      rwa [sq_abs] at this
    set δ := 2 * (r2 ^ 2 - (x - x0) ^ 2) / (9 - r2 ^ 2)
    have hδ_lo : 2 * (r2 ^ 2 - r1 ^ 2) / (9 - r2 ^ 2) ≤ δ :=
      div_le_div_of_nonneg_right (by linarith) h9_pos.le
    have hδ0 : 0 ≤ δ :=
      le_trans (div_nonneg (by nlinarith) h9_pos.le) hδ_lo
    have hδ_le : δ ≤ 2 * r2 ^ 2 / (9 - r2 ^ 2) :=
      div_le_div_of_nonneg_right (by nlinarith) h9_pos.le
    have hlδ : (l : ℝ) ^ 2 * δ ≤ 1 / 5 :=
      (mul_le_mul_of_nonneg_left hδ_le (sq_nonneg _)).trans hl_δ0
    have heval : (uQuadPoly x0 r2).eval x = 1 + δ := eval_uQuadPoly x0 r2 x
    rw [heval]
    obtain ⟨hlo, _⟩ := chebT_passband l hδ0 hlδ
    have hη_le_lδ : η ≤ (l : ℝ) ^ 2 * δ := by
      rw [hη_eq]
      exact mul_le_mul_of_nonneg_left hδ_lo (sq_nonneg _)
    have hT_ge : 1 + η ≤ (Polynomial.Chebyshev.T ℝ l).eval (1 + δ) := by linarith
    have hT_sq : (1 + η) ^ 2 ≤ ((Polynomial.Chebyshev.T ℝ l).eval (1 + δ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hT_ge 2
    rw [le_div_iff₀ h2η_pos]
    nlinarith

private noncomputable def taylorUnitPoly (n : ℕ) : ℝ[X] :=
  ∑ m ∈ Finset.range n, C (1 / (m.factorial : ℝ)) * X ^ m

private lemma eval_taylorUnitPoly (n : ℕ) (y : ℝ) :
    (taylorUnitPoly n).eval y = ∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ) := by
  simp [taylorUnitPoly, eval_finsetSum, div_eq_inv_mul]

private lemma natDegree_taylorUnitPoly_le (n : ℕ) :
    (taylorUnitPoly n).natDegree ≤ n := by
  dsimp [taylorUnitPoly]
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le n, fun m hm => ?_⟩
  rw [Finset.mem_range] at hm
  refine le_trans natDegree_mul_le ?_
  simp only [natDegree_C, zero_add, natDegree_pow, natDegree_X, mul_one]
  omega

private lemma two_pow_le_factorial (n : ℕ) : 2 ^ (n - 1) ≤ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [Nat.succ_sub_one, pow_succ', Nat.factorial_succ]
      exact Nat.mul_le_mul (by omega) ih

private lemma taylorUnit_approx {y : ℝ} (hy : |y| ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    |(taylorUnitPoly n).eval y - Real.exp y| ≤ 4 / (2 : ℝ) ^ n := by
  rw [eval_taylorUnitPoly, abs_sub_comm]
  have heb := Real.exp_bound hy (by omega : 0 < n)
  have hy_pow : |y| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
  have hfac_nat : 2 ^ (n - 1) * n ≤ n.factorial * n :=
    Nat.mul_le_mul_right n (two_pow_le_factorial n)
  have hfac : (2 : ℝ) ^ (n - 1) * (n : ℝ) ≤ (n.factorial : ℝ) * (n : ℝ) := by
    exact_mod_cast hfac_nat
  have hsucc : (n.succ : ℝ) ≤ 2 * (n : ℝ) := by
    have : n + 1 ≤ 2 * n := by omega
    exact_mod_cast this
  have h2pow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']
  have hpos_fac : (0 : ℝ) < (n.factorial : ℝ) * (n : ℝ) := by positivity
  have hpos_2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hdiv : (n.succ : ℝ) / ((n.factorial : ℝ) * (n : ℝ)) ≤ 4 / (2 : ℝ) ^ n := by
    rw [div_le_div_iff₀ hpos_fac hpos_2n, h2pow]
    nlinarith
  have hmul : |y| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * (n : ℝ))) ≤
      1 * (4 / (2 : ℝ) ^ n) :=
    mul_le_mul hy_pow hdiv (by positivity) zero_le_one
  linarith

private lemma abs_pow_sub_pow_le' (M : ℕ) {a b B : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) :
    |a ^ M - b ^ M| ≤ (M : ℝ) * B ^ (M - 1) * |a - b| := by
  induction M with
  | zero => simp
  | succ M ih =>
    cases M with
    | zero => simp
    | succ m =>
      change |a ^ (m + 2) - b ^ (m + 2)| ≤ ((m + 2 : ℕ) : ℝ) * B ^ (m + 1) * |a - b|
      have hid : a ^ (m + 2) - b ^ (m + 2) =
          a * (a ^ (m + 1) - b ^ (m + 1)) + (a - b) * b ^ (m + 1) := by
        simp only [pow_succ']; ring
      have hbm : |b ^ (m + 1)| ≤ B ^ (m + 1) := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg b) hb (m + 1)
      have h1 : |a ^ (m + 2) - b ^ (m + 2)| ≤
          |a| * |a ^ (m + 1) - b ^ (m + 1)| + |a - b| * |b ^ (m + 1)| := by
        rw [hid]
        exact (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le (abs_mul _ _).le)
      have h2 : |a| * |a ^ (m + 1) - b ^ (m + 1)| ≤
          B * (((m + 1 : ℕ) : ℝ) * B ^ m * |a - b|) :=
        mul_le_mul ha (by simpa using ih) (abs_nonneg _) hB
      have h3 : |a - b| * |b ^ (m + 1)| ≤ |a - b| * B ^ (m + 1) :=
        mul_le_mul_of_nonneg_left hbm (abs_nonneg _)
      have h4 : B * (((m + 1 : ℕ) : ℝ) * B ^ m * |a - b|) + |a - b| * B ^ (m + 1) =
          ((m + 2 : ℕ) : ℝ) * B ^ (m + 1) * |a - b| := by
        push_cast
        rw [pow_succ']
        ring
      exact (h1.trans (add_le_add h2 h3)).trans_eq h4

private lemma taylorUnit_global_bound {y B : ℝ} (hB : 1 ≤ B) (hy : |y| ≤ B) (n : ℕ) :
    |(taylorUnitPoly n).eval y| ≤ (n : ℝ) * B ^ n := by
  rw [eval_taylorUnitPoly]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ Finset.range n, |y ^ m / (m.factorial : ℝ)| ≤ B ^ n := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [abs_div, abs_pow, Nat.abs_cast]
    have hfac : (1 : ℝ) ≤ (m.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos m
    have h1 : |y| ^ m / (m.factorial : ℝ) ≤ |y| ^ m / 1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hfac
    have h2 : |y| ^ m ≤ B ^ m := pow_le_pow_left₀ (abs_nonneg y) hy m
    have h3 : B ^ m ≤ B ^ n := pow_le_pow_right₀ hB (by omega)
    linarith
  calc ∑ m ∈ Finset.range n, |y ^ m / (m.factorial : ℝ)|
    _ ≤ ∑ _m ∈ Finset.range n, B ^ n := Finset.sum_le_sum hterm
    _ = (n : ℝ) * B ^ n := by simp

private lemma exp_le_four_pow (x : ℝ) :
    Real.exp x ≤ (4 : ℝ) ^ (Nat.ceil x) := by
  have h1 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have h2 : Real.exp x ≤ Real.exp ((Nat.ceil x : ℝ) * 1) := by
    rw [mul_one]
    exact Real.exp_le_exp.mpr h1
  rw [Real.exp_nat_mul] at h2
  have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
  exact h2.trans (pow_le_pow_left₀ (Real.exp_pos 1).le he4 _)

private lemma floor_ge_half {z : ℝ} (hz : 1 ≤ z) : z / 2 ≤ (Nat.floor z : ℝ) := by
  by_cases h2 : z < 2
  · have hf : Nat.floor z = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by norm_num; exact hz, by norm_num; exact h2⟩
    rw [hf]
    linarith
  · have hlt : z - 1 < (Nat.floor z : ℝ) := Nat.sub_one_lt_floor z
    linarith

private lemma nat_le_two_pow (m : ℕ) : (m : ℝ) ≤ (2 : ℝ) ^ m := by
  exact_mod_cast (Nat.lt_two_pow_self (n := m)).le

private lemma nat_log_bounds {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) ∧
    (2 : ℝ) ^ (Nat.log 2 N + 1) ≤ 2 * (N : ℝ) := by
  constructor
  · have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self one_lt_two N
    exact_mod_cast hlt.le
  · have hle : 2 ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hleR : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by exact_mod_cast hle
    rw [pow_succ']
    linarith

private noncomputable def EApproxPoly (n M : ℕ) (β : ℝ) : ℝ[X] :=
  C (1 / 4 : ℝ) * ((taylorUnitPoly n).comp (C (2 * β / (M : ℝ)) * X)) ^ M

private lemma eval_EApproxPoly (n M : ℕ) (β x : ℝ) :
    (EApproxPoly n M β).eval x =
      (1 / 4 : ℝ) * ((taylorUnitPoly n).eval (2 * β * x / (M : ℝ))) ^ M := by
  dsimp [EApproxPoly]
  simp only [eval_mul, eval_C, eval_pow, eval_comp, eval_X]
  ring_nf

private lemma natDegree_EApproxPoly_le (n M : ℕ) (β : ℝ) :
    (EApproxPoly n M β).natDegree ≤ M * n := by
  dsimp [EApproxPoly]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_pow_le).trans ?_
  refine Nat.mul_le_mul_left M ?_
  refine natDegree_comp_le.trans ?_
  have h1 : (C (2 * β / (M : ℝ)) * X).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_; simp
  calc (taylorUnitPoly n).natDegree * (C (2 * β / (M : ℝ)) * X).natDegree
    _ ≤ n * 1 := Nat.mul_le_mul (natDegree_taylorUnitPoly_le n) h1
    _ = n := Nat.mul_one n

private lemma EApproxPoly_active_bound {n M KR : ℕ} {β x : ℝ} (hM : 1 ≤ M)
    (hn : n = 3 * M + 2 + 2 * KR) (hy : |2 * β * x / (M : ℝ)| ≤ 1) :
    |(EApproxPoly n M β).eval x - Real.exp (2 * β * x) / 4| ≤
      1 / (4 * (4 : ℝ) ^ KR) := by
  rw [eval_EApproxPoly]
  set y := 2 * β * x / (M : ℝ)
  have hM_ne : (M : ℝ) ≠ 0 := by positivity
  have hexp_eq : Real.exp (2 * β * x) = (Real.exp y) ^ M := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [y]
    field_simp [hM_ne]
  rw [hexp_eq]
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have htay := taylorUnit_approx hy hn1
  have h2n_ge4 : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn2
  have htay1 : |(taylorUnitPoly n).eval y - Real.exp y| ≤ 1 := by
    have : 4 / (2 : ℝ) ^ n ≤ 4 / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2n_ge4
    linarith
  have hy_hi : y ≤ 1 := (abs_le.mp hy).2
  have hexp_le3 : Real.exp y ≤ 3 := by
    have h1 : Real.exp y ≤ Real.exp 1 := Real.exp_le_exp.mpr hy_hi
    linarith [Real.exp_one_lt_d9]
  have hexp_abs3 : |Real.exp y| ≤ 3 := by
    rw [abs_of_pos (Real.exp_pos y)]
    exact hexp_le3
  have hexp_abs : |Real.exp y| ≤ 4 := by linarith only [hexp_abs3]
  have htay_abs : |(taylorUnitPoly n).eval y| ≤ 4 := by
    have hsub := (abs_sub_abs_le_abs_sub ((taylorUnitPoly n).eval y) (Real.exp y)).trans htay1
    linarith only [sub_le_iff_le_add.mp hsub, hexp_abs3]
  have hpow := abs_pow_sub_pow_le' M (by norm_num : (0 : ℝ) ≤ 4) htay_abs hexp_abs
  have hM_pow : (M : ℝ) ≤ (2 : ℝ) ^ M := nat_le_two_pow M
  have h4M : (4 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ (2 * M) := by
    calc (4 : ℝ) ^ (M - 1) ≤ (4 : ℝ) ^ M :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
      _ = ((2 : ℝ) ^ 2) ^ M := by norm_num
      _ = (2 : ℝ) ^ (2 * M) := by rw [← pow_mul]
  have hdiff : |(1 / 4 : ℝ) * ((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M / 4| =
      (1 / 4 : ℝ) * |((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M| := by
    have : (1 / 4 : ℝ) * ((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M / 4 =
        (1 / 4 : ℝ) * (((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  rw [hdiff]
  have hstep1 : |((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M| ≤
      (M : ℝ) * (4 : ℝ) ^ (M - 1) * (4 / (2 : ℝ) ^ n) :=
    hpow.trans (mul_le_mul_of_nonneg_left htay (by positivity))
  have hstep2 : |((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M| ≤ 1 / (4 : ℝ) ^ KR := by
    have h1 : (M : ℝ) * (4 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M * (2 : ℝ) ^ (2 * M) :=
      mul_le_mul hM_pow h4M (by positivity) (by positivity)
    have h2 : (2 : ℝ) ^ M * (2 : ℝ) ^ (2 * M) * 4 = (2 : ℝ) ^ (3 * M + 2) := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, ← pow_add, ← pow_add]
      congr 1
      omega
    have h2n_eq : (2 : ℝ) ^ n = (2 : ℝ) ^ (3 * M + 2) * (4 : ℝ) ^ KR := by
      rw [hn, pow_add, pow_mul]
      norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (3 * M + 2) * (4 : ℝ) ^ KR := by positivity
    have hdiv : (M : ℝ) * (4 : ℝ) ^ (M - 1) * (4 / (2 : ℝ) ^ n) ≤ 1 / (4 : ℝ) ^ KR := by
      rw [h2n_eq]
      calc (M : ℝ) * (4 : ℝ) ^ (M - 1) * (4 / ((2 : ℝ) ^ (3 * M + 2) * (4 : ℝ) ^ KR))
        _ = ((M : ℝ) * (4 : ℝ) ^ (M - 1) * 4) / ((2 : ℝ) ^ (3 * M + 2) * (4 : ℝ) ^ KR) := by ring
        _ ≤ ((2 : ℝ) ^ (3 * M + 2)) / ((2 : ℝ) ^ (3 * M + 2) * (4 : ℝ) ^ KR) := by
            refine div_le_div_of_nonneg_right ?_ hpos.le
            linarith
        _ = 1 / (4 : ℝ) ^ KR := by
            have hne : (2 : ℝ) ^ (3 * M + 2) ≠ 0 := by positivity
            field_simp [hne]
    exact hstep1.trans hdiv
  calc (1 / 4 : ℝ) * |((taylorUnitPoly n).eval y) ^ M - (Real.exp y) ^ M|
    _ ≤ (1 / 4 : ℝ) * (1 / (4 : ℝ) ^ KR) :=
        mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ = 1 / (4 * (4 : ℝ) ^ KR) := by ring

private lemma EApproxPoly_global_bound (n M : ℕ) {β x : ℝ} (hM : 1 ≤ M)
    (hβ : 1 ≤ β) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(EApproxPoly n M β).eval x| ≤ (4 * β) ^ (n * M) := by
  rw [eval_EApproxPoly, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_pow]
  set y := 2 * β * x / (M : ℝ)
  have hM_ge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hx_abs : |x| ≤ 1 := abs_le.mpr hx
  have hy_abs : |y| ≤ 2 * β := by
    dsimp [y]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by positivity : 0 < β), abs_of_pos (by positivity : (0 : ℝ) < M)]
    have h1 : 2 * β * |x| ≤ 2 * β * 1 :=
      mul_le_mul_of_nonneg_left hx_abs (by positivity)
    have h2 : 2 * β * |x| / (M : ℝ) ≤ 2 * β * |x| / 1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hM_ge1
    linarith
  have htay := taylorUnit_global_bound (by linarith : 1 ≤ 2 * β) hy_abs n
  have hn_pow : (n : ℝ) ≤ (2 : ℝ) ^ n := nat_le_two_pow n
  have htay2 : |(taylorUnitPoly n).eval y| ≤ (4 * β) ^ n := by
    calc |(taylorUnitPoly n).eval y|
      _ ≤ (n : ℝ) * (2 * β) ^ n := htay
      _ ≤ (2 : ℝ) ^ n * (2 * β) ^ n :=
          mul_le_mul_of_nonneg_right hn_pow (by positivity)
      _ = (4 * β) ^ n := by rw [← mul_pow]; ring
  have hpow : |(taylorUnitPoly n).eval y| ^ M ≤ ((4 * β) ^ n) ^ M :=
    pow_le_pow_left₀ (abs_nonneg _) htay2 M
  rw [← pow_mul] at hpow
  have hpos : 0 ≤ (4 * β) ^ (n * M) := by positivity
  linarith

private lemma window_params_exist {β R : ℝ}
    (hβ1 : 1 ≤ β) (hR4 : 4 ≤ R) :
    ∃ (x0 r1 r2 η : ℝ) (l : ℕ),
      -1 / 2 ≤ x0 ∧ x0 ≤ 0 ∧
      0 < r1 ∧ r1 ≤ r2 ∧ r2 ≤ 5 / 8 ∧
      x0 + r1 = 0 ∧ x0 - r1 = -min R β / β ∧
      x0 + r2 = 1 / (8 * β) ∧ x0 - r2 = -(2 * min R β + 1 / 4) / (2 * β) ∧
      (l : ℝ) ≤ 2 * β ∧
      (l : ℝ) ^ 2 * (2 * r2 ^ 2 / (9 - r2 ^ 2)) ≤ 1 / 5 ∧
      η = (l : ℝ) ^ 2 * (2 * (r2 ^ 2 - r1 ^ 2) / (9 - r2 ^ 2)) ∧
      1 / (225 * R) ≤ η ∧ η ≤ 1 / 5 := by
  set R0 := min R β
  set x0 := -R0 / (2 * β)
  set r1 := R0 / (2 * β)
  set r2 := (4 * R0 + 1) / (8 * β)
  have hR0_ge1 : 1 ≤ R0 := le_min (by linarith) hβ1
  have hR0_le_R : R0 ≤ R := min_le_left _ _
  have hR0_le_β : R0 ≤ β := min_le_right _ _
  have hx0_lo : -1 / 2 ≤ x0 := by
    dsimp [x0]; rw [le_div_iff₀ (by positivity)]; linarith
  have hx0_hi : x0 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hr1_pos : 0 < r1 := by dsimp [r1]; positivity
  have hr12 : r1 ≤ r2 := by
    dsimp [r1, r2]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hr2_pos : 0 < r2 := by dsimp [r2]; positivity
  have hr2_le : r2 ≤ 5 / 8 := by
    dsimp [r2]; rw [div_le_iff₀ (by positivity)]; linarith
  have hr2_le_R : r2 ≤ (5 * R) / (8 * β) := by
    dsimp [r2]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h9_r2 : 8 ≤ 9 - r2 ^ 2 ∧ 9 - r2 ^ 2 ≤ 9 := ⟨by nlinarith, by nlinarith⟩
  set l := Nat.floor (4 / (5 * r2))
  have h4_5r2_ge1 : 1 ≤ 4 / (5 * r2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hl_lo : 2 / (5 * r2) ≤ (l : ℝ) := by
    have h := floor_ge_half h4_5r2_ge1
    have heq : 4 / (5 * r2) / 2 = 2 / (5 * r2) := by ring
    rwa [heq] at h
  have hl_hi : (l : ℝ) ≤ 4 / (5 * r2) := Nat.floor_le (by positivity)
  have h8βr2 : 8 * β * r2 = 4 * R0 + 1 := by
    dsimp [r2]; field_simp
  have hl_le_2β : (l : ℝ) ≤ 2 * β := by
    have : 4 / (5 * r2) ≤ 2 * β := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  set δ0 := 2 * r2 ^ 2 / (9 - r2 ^ 2)
  set δ1 := 2 * (r2 ^ 2 - r1 ^ 2) / (9 - r2 ^ 2)
  have hδ0_nonneg : 0 ≤ δ0 := div_nonneg (by positivity) (by linarith)
  have hr2_sub_r1 : r2 - r1 = 1 / (8 * β) := by dsimp [r2, r1]; ring
  have hr2_sq_sub : r2 / (8 * β) ≤ r2 ^ 2 - r1 ^ 2 := by
    have h1 : r2 ^ 2 - r1 ^ 2 = (r2 - r1) * (r2 + r1) := by ring
    rw [h1, hr2_sub_r1]
    have h2 : 1 / (8 * β) * r2 ≤ 1 / (8 * β) * (r2 + r1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 1 / (8 * β) * r2 = r2 / (8 * β) := by ring
    linarith
  have hδ1_lo : r2 / (36 * β) ≤ δ1 := by
    dsimp [δ1]
    rw [le_div_iff₀ (by linarith)]
    have h1 : r2 / (36 * β) * (9 - r2 ^ 2) ≤ r2 / (36 * β) * 9 :=
      mul_le_mul_of_nonneg_left h9_r2.2 (by positivity)
    have h2 : r2 / (36 * β) * 9 = 2 * (r2 / (8 * β)) := by ring
    linarith
  have hδ0_hi : δ0 ≤ r2 ^ 2 / 4 := by
    dsimp [δ0]; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hl2_δ0 : (l : ℝ) ^ 2 * δ0 ≤ 1 / 5 := by
    have h1 : (l : ℝ) ^ 2 ≤ (4 / (5 * r2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hl_hi 2
    have h2 : (l : ℝ) ^ 2 * δ0 ≤ (4 / (5 * r2)) ^ 2 * (r2 ^ 2 / 4) :=
      mul_le_mul h1 hδ0_hi hδ0_nonneg (by positivity)
    have h3 : (4 / (5 * r2)) ^ 2 * (r2 ^ 2 / 4) = 4 / 25 := by
      field_simp [hr2_pos.ne']; ring
    linarith
  set η := (l : ℝ) ^ 2 * δ1
  have hδ1_le_δ0 : δ1 ≤ δ0 := by
    dsimp [δ1, δ0]
    exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  have hη_le : η ≤ 1 / 5 :=
    (mul_le_mul_of_nonneg_left hδ1_le_δ0 (sq_nonneg _)).trans hl2_δ0
  have hη_lo : 1 / (225 * R) ≤ η := by
    have h1 : (2 / (5 * r2)) ^ 2 ≤ (l : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hl_lo 2
    have h2 : (2 / (5 * r2)) ^ 2 * (r2 / (36 * β)) ≤ η :=
      mul_le_mul h1 hδ1_lo (by positivity) (sq_nonneg _)
    have h3 : (2 / (5 * r2)) ^ 2 * (r2 / (36 * β)) = 1 / (225 * β * r2) := by
      field_simp [hr2_pos.ne']; ring
    have h4 : β * r2 ≤ R := by linarith
    have h5 : 1 / (225 * R) ≤ 1 / (225 * β * r2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  refine ⟨x0, r1, r2, η, l, hx0_lo, hx0_hi, hr1_pos, hr12, hr2_le, ?_, ?_, ?_, ?_,
    hl_le_2β, hl2_δ0, rfl, hη_lo, hη_le⟩
  · dsimp [x0, r1]; ring
  · dsimp [x0, r1, R0]; ring
  · dsimp [x0, r2]; ring
  · dsimp [x0, r2, R0]; ring

private lemma product_eval_bounds (EPoly WPoly : ℝ[X]) {ξ β R x0 r1 r2 B_E δ_W : ℝ}
    (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) (hβ1 : 1 ≤ β)
    (hx0_r1 : x0 + r1 = 0) (hx0_sub_r1 : x0 - r1 = -min R β / β)
    (hx0_r2 : x0 + r2 = 1 / (8 * β)) (hr12 : r1 ≤ r2)
    (h8ξ_expR : 8 / ξ ≤ Real.exp R)
    (hBE1 : 1 ≤ B_E) (hδW_nonneg : 0 ≤ δ_W) (hstop_prod : B_E * δ_W ≤ ξ / 16)
    (hW_Icc : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ WPoly.eval x ∧ WPoly.eval x ≤ 1)
    (hW_stop : ∀ x ∈ Set.Icc (-1 : ℝ) 1, r2 ≤ |x - x0| → WPoly.eval x ≤ δ_W)
    (hW_pass : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |x - x0| ≤ r1 → |WPoly.eval x - 1| ≤ δ_W)
    (hE_active : ∀ x : ℝ, |x - x0| ≤ r2 →
      |EPoly.eval x - Real.exp (2 * β * x) / 4| ≤ ξ / 32)
    (hE_global : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |EPoly.eval x| ≤ B_E) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 0,
      |(EPoly * WPoly).eval x - Real.exp (2 * β * x) / 4| ≤ ξ) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(EPoly * WPoly).eval x| ≤ 1 / 2) := by
  have hδW_le : δ_W ≤ ξ / 16 := by
    calc δ_W = 1 * δ_W := (one_mul _).symm
      _ ≤ B_E * δ_W := mul_le_mul_of_nonneg_right hBE1 hδW_nonneg
      _ ≤ ξ / 16 := hstop_prod
  have htail_exp : ∀ x ∈ Set.Icc (-1 : ℝ) 0, r1 < |x - x0| →
      Real.exp (2 * β * x) / 4 ≤ ξ / 32 := by
    intro x hx hrx
    have hx_neg : x ≤ 0 := hx.2
    have hx_ge : -1 ≤ x := hx.1
    have hx_lt : x < -min R β / β := by
      rw [lt_abs] at hrx
      rcases hrx with h1 | h1
      · exfalso; linarith
      · linarith
    have hR0_lt_β : min R β < β := by
      have h1 : -1 < -min R β / β := lt_of_le_of_lt hx_ge hx_lt
      have h2 := (lt_div_iff₀ (by positivity : 0 < β)).mp h1
      linarith
    have hR0_eq_R : min R β = R := by
      rcases le_total R β with h | h
      · exact min_eq_left h
      · exfalso; rw [min_eq_right h] at hR0_lt_β; exact lt_irrefl β hR0_lt_β
    have h2βx : 2 * β * x ≤ -R := by
      rw [hR0_eq_R] at hx_lt
      have h1 := (lt_div_iff₀ (by positivity : 0 < β)).mp hx_lt
      have h1' : β * x < -R := by linarith [(by ring : x * β = β * x)]
      have h2' : β * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hx_neg
      linarith
    have h1 : Real.exp (2 * β * x) ≤ Real.exp (-R) := Real.exp_le_exp.mpr h2βx
    have h2 : Real.exp (-R) = 1 / Real.exp R := by rw [Real.exp_neg, one_div]
    have h3 : 1 / Real.exp R ≤ 1 / (8 / ξ) :=
      one_div_le_one_div_of_le (by positivity) h8ξ_expR
    have h4 : 1 / (8 / ξ) = ξ / 8 := by field_simp
    linarith
  constructor
  · intro x hx
    rw [eval_mul]
    have hx_Icc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    rcases le_or_gt |x - x0| r1 with hrx1 | hrx1
    · have hE := hE_active x (hrx1.trans hr12)
      have hexp_le : Real.exp (2 * β * x) / 4 ≤ 1 / 4 := by
        have : Real.exp (2 * β * x) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith [hx.2])
        rw [Real.exp_zero] at this
        linarith
      have hE_abs : |EPoly.eval x| ≤ 1 := by
        have := abs_sub_abs_le_abs_sub (EPoly.eval x) (Real.exp (2 * β * x) / 4)
        have hexp_pos : 0 < Real.exp (2 * β * x) / 4 := by positivity
        rw [abs_of_pos hexp_pos] at this
        linarith
      have hW := (hW_pass x hx_Icc hrx1).trans hδW_le
      have hid : EPoly.eval x * WPoly.eval x - Real.exp (2 * β * x) / 4 =
          EPoly.eval x * (WPoly.eval x - 1) +
            (EPoly.eval x - Real.exp (2 * β * x) / 4) := by ring
      rw [hid]
      have hmul : |EPoly.eval x * (WPoly.eval x - 1)| ≤ 1 * (ξ / 16) := by
        rw [abs_mul]
        exact mul_le_mul hE_abs hW (abs_nonneg _) zero_le_one
      have htri := abs_add_le (EPoly.eval x * (WPoly.eval x - 1))
        (EPoly.eval x - Real.exp (2 * β * x) / 4)
      linarith
    · have hexp_tail := htail_exp x hx hrx1
      have hexp_pos : 0 < Real.exp (2 * β * x) / 4 := by positivity
      rcases le_or_gt |x - x0| r2 with hrx2 | hrx2
      · have hE := hE_active x hrx2
        have hE_abs : |EPoly.eval x| ≤ ξ / 16 := by
          have := abs_sub_abs_le_abs_sub (EPoly.eval x) (Real.exp (2 * β * x) / 4)
          rw [abs_of_pos hexp_pos] at this
          linarith
        have hW01 := hW_Icc x hx_Icc
        have hEW : |EPoly.eval x * WPoly.eval x| ≤ ξ / 16 := by
          rw [abs_mul, abs_of_nonneg hW01.1]
          calc |EPoly.eval x| * WPoly.eval x
            _ ≤ (ξ / 16) * 1 := mul_le_mul hE_abs hW01.2 hW01.1 (by positivity)
            _ = ξ / 16 := mul_one _
        have htri := abs_sub (EPoly.eval x * WPoly.eval x) (Real.exp (2 * β * x) / 4)
        rw [abs_of_pos hexp_pos] at htri
        linarith
      · have hE := hE_global x hx_Icc
        have hW0 := (hW_Icc x hx_Icc).1
        have hW := hW_stop x hx_Icc hrx2.le
        have hEW : |EPoly.eval x * WPoly.eval x| ≤ ξ / 16 := by
          rw [abs_mul, abs_of_nonneg hW0]
          exact (mul_le_mul hE hW hW0 (by linarith)).trans hstop_prod
        have htri := abs_sub (EPoly.eval x * WPoly.eval x) (Real.exp (2 * β * x) / 4)
        rw [abs_of_pos hexp_pos] at htri
        linarith
  · intro x hx
    rw [eval_mul]
    rcases le_or_gt |x - x0| r2 with hrx2 | hrx2
    · have hE := hE_active x hrx2
      have h2βx_hi : 2 * β * x ≤ 1 / 4 := by
        have hx_hi : x ≤ 1 / (8 * β) := by linarith [(abs_le.mp hrx2).2]
        have h3 := (le_div_iff₀ (by positivity : 0 < 8 * β)).mp hx_hi
        linarith
      have hexp_le : Real.exp (2 * β * x) / 4 ≤ 3 / 8 := by
        rcases le_or_gt (2 * β * x) 0 with hneg | hpos
        · have : Real.exp (2 * β * x) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
          rw [Real.exp_zero] at this
          linarith
        · have habs : |2 * β * x| ≤ 1 := by rw [abs_of_pos hpos]; linarith
          have hsub := Real.abs_exp_sub_one_le habs
          rw [abs_of_pos hpos] at hsub
          have : Real.exp (2 * β * x) - 1 ≤ 2 * (2 * β * x) := (abs_le.mp hsub).2
          linarith
      have hE_abs : |EPoly.eval x| ≤ 1 / 2 := by
        have := abs_sub_abs_le_abs_sub (EPoly.eval x) (Real.exp (2 * β * x) / 4)
        have hexp_pos : 0 < Real.exp (2 * β * x) / 4 := by positivity
        rw [abs_of_pos hexp_pos] at this
        linarith
      have hW01 := hW_Icc x hx
      rw [abs_mul, abs_of_nonneg hW01.1]
      calc |EPoly.eval x| * WPoly.eval x
        _ ≤ (1 / 2) * 1 := mul_le_mul hE_abs hW01.2 hW01.1 (by norm_num)
        _ = 1 / 2 := mul_one _
    · have hE := hE_global x hx
      have hW0 := (hW_Icc x hx).1
      have hW := hW_stop x hx hrx2.le
      rw [abs_mul, abs_of_nonneg hW0]
      have hEW := (mul_le_mul hE hW hW0 (by linarith)).trans hstop_prod
      linarith

private lemma exp_three_ge_eight : (8 : ℝ) ≤ Real.exp 3 := by
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    have : (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 := by norm_num
    rw [this, Real.exp_nat_mul]
  rw [h3]
  calc (8 : ℝ) = 2 ^ 3 := by norm_num
    _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3

private lemma degree_and_exp_bounds {ξ β η : ℝ} {l : ℕ}
    (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) (hβ1 : 1 ≤ β)
    (hl_le : (l : ℝ) ≤ 2 * β)
    (hη_lo : 1 / (225 * (Real.log (2 + 1 / ξ) + 3)) ≤ η) :
    ∃ (M KR n s1 s2 : ℕ),
      1 ≤ M ∧ n = 3 * M + 2 + 2 * KR ∧
      2 * (Real.log (2 + 1 / ξ) + 3) + 1 ≤ (M : ℝ) ∧
      8 / ξ ≤ Real.exp (Real.log (2 + 1 / ξ) + 3) ∧
      1 / (4 * (4 : ℝ) ^ KR) ≤ ξ / 32 ∧
      1 / 3 ≤ (5 / 4 : ℝ) ^ s1 * (η / 5) ∧
      (4 * β) ^ (n * M) * ((1 / 3) * (1 / 2) ^ (2 ^ s2)) ≤ ξ / 16 ∧
      ((M * n + 3 ^ (s1 + s2) * (4 * l) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ 130 * β * (Real.log (2 + β) + Real.log (2 + 1 / ξ)) ^ 15 := by
  obtain ⟨Lβ, hLβ_def⟩ : ∃ Lβ : ℝ, Lβ = Real.log (2 + β) := ⟨_, rfl⟩
  obtain ⟨Lξ, hLξ_def⟩ : ∃ Lξ : ℝ, Lξ = Real.log (2 + 1 / ξ) := ⟨_, rfl⟩
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = Lβ + Lξ := ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = Lξ + 3 := ⟨_, rfl⟩
  have h1_ξ : 6 ≤ 1 / ξ := by rw [le_div_iff₀ hξ0]; linarith only [hξ1]
  have hLβ_ge1 : 1 ≤ Lβ := by
    rw [hLβ_def]
    have hexp1 : Real.exp 1 ≤ 2 + β := by linarith only [Real.exp_one_lt_d9, hβ1]
    have h := Real.log_le_log (Real.exp_pos 1) hexp1
    rwa [Real.log_exp] at h
  have hLξ_ge1 : 1 ≤ Lξ := by
    rw [hLξ_def]
    have hexp1 : Real.exp 1 ≤ 2 + 1 / ξ := by linarith only [Real.exp_one_lt_d9, h1_ξ]
    have h := Real.log_le_log (Real.exp_pos 1) hexp1
    rwa [Real.log_exp] at h
  have hL_ge2 : 2 ≤ L := by linarith only [hL_def, hLβ_ge1, hLξ_ge1]
  have hR_ge4 : 4 ≤ R := by linarith only [hR_def, hLξ_ge1]
  have hL_pos : 0 < L := by linarith only [hL_ge2]
  have hR_pos : 0 < R := by linarith only [hR_ge4]
  have hLβ_pos : 0 < Lβ := by linarith only [hLβ_ge1]
  have hLξ_pos : 0 < Lξ := by linarith only [hLξ_ge1]
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = Nat.ceil (2 * R + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨KR, hKR_def⟩ : ∃ KR : ℕ, KR = Nat.ceil R := ⟨_, rfl⟩
  obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = 3 * M + 2 + 2 * KR := ⟨_, rfl⟩
  obtain ⟨K1, hK1_def⟩ : ∃ K1 : ℕ, K1 = Nat.ceil (1125 * R) := ⟨_, rfl⟩
  obtain ⟨k1, hk1_def⟩ : ∃ k1 : ℕ, k1 = Nat.log 2 K1 + 1 := ⟨_, rfl⟩
  obtain ⟨s1, hs1_def⟩ : ∃ s1 : ℕ, s1 = 4 * k1 := ⟨_, rfl⟩
  obtain ⟨KLβ, hKLβ_def⟩ : ∃ KLβ : ℕ, KLβ = Nat.ceil Lβ := ⟨_, rfl⟩
  obtain ⟨KLξ, hKLξ_def⟩ : ∃ KLξ : ℕ, KLξ = Nat.ceil Lξ := ⟨_, rfl⟩
  obtain ⟨N2, hN2_def⟩ : ∃ N2 : ℕ, N2 = n * M * (2 * KLβ + 2) + 2 * KLξ + 4 := ⟨_, rfl⟩
  obtain ⟨s2, hs2_def⟩ : ∃ s2 : ℕ, s2 = Nat.log 2 N2 + 1 := ⟨_, rfl⟩
  have hM_ge1 : 1 ≤ M := by omega
  have hM_lo : 2 * (Real.log (2 + 1 / ξ) + 3) + 1 ≤ (M : ℝ) := by
    rw [← hLξ_def, ← hR_def]
    have h1 : 2 * R + 1 ≤ (Nat.ceil (2 * R + 1) : ℝ) := Nat.le_ceil (2 * R + 1)
    have h2 : (M : ℝ) = (Nat.ceil (2 * R + 1) : ℝ) + 1 := by rw [hM_def]; push_cast; rfl
    linarith only [h1, h2]
  have h8ξ_expR : 8 / ξ ≤ Real.exp R := by
    have h2 : Real.exp R = (2 + 1 / ξ) * Real.exp 3 := by
      rw [hR_def, hLξ_def, Real.exp_add, Real.exp_log (by positivity)]
    have he3 := exp_three_ge_eight
    have h3 : 8 * (1 / ξ) ≤ (2 + 1 / ξ) * Real.exp 3 := by
      calc 8 * (1 / ξ) ≤ (2 + 1 / ξ) * 8 := by linarith only [h1_ξ]
        _ ≤ (2 + 1 / ξ) * Real.exp 3 := mul_le_mul_of_nonneg_left he3 (by linarith only [h1_ξ])
    have h4 : 8 / ξ = 8 * (1 / ξ) := by ring
    linarith only [h2, h3, h4]
  have h8ξ_expR' : 8 / ξ ≤ Real.exp (Real.log (2 + 1 / ξ) + 3) := by
    rwa [← hLξ_def, ← hR_def]
  have h4KR_lo : 8 / ξ ≤ (4 : ℝ) ^ KR := by
    rw [hKR_def]
    exact h8ξ_expR.trans (exp_le_four_pow R)
  have h1_4KR : 1 / (4 * (4 : ℝ) ^ KR) ≤ ξ / 32 := by
    have : 32 / ξ ≤ 4 * (4 : ℝ) ^ KR := by
      calc 32 / ξ = 4 * (8 / ξ) := by ring
        _ ≤ 4 * (4 : ℝ) ^ KR := mul_le_mul_of_nonneg_left h4KR_lo (by norm_num)
    have hdiv := one_div_le_one_div_of_le (by positivity : 0 < 32 / ξ) this
    have hsimp : 1 / (32 / ξ) = ξ / 32 := by field_simp
    rwa [hsimp] at hdiv
  have hK1_lo : 1125 * R ≤ (K1 : ℝ) := by rw [hK1_def]; exact Nat.le_ceil _
  have hK1_ge1 : 1 ≤ K1 := by
    have h1 : (1 : ℝ) ≤ (K1 : ℝ) := by linarith only [hK1_lo, hR_ge4]
    exact_mod_cast h1
  have hk1_bounds : (K1 : ℝ) ≤ (2 : ℝ) ^ k1 ∧ (2 : ℝ) ^ k1 ≤ 2 * (K1 : ℝ) := by
    rw [hk1_def]; exact nat_log_bounds hK1_ge1
  have hs1_amp : 1 / 3 ≤ (5 / 4 : ℝ) ^ s1 * (η / 5) := by
    have h54_pow : (2 : ℝ) ^ k1 ≤ (5 / 4 : ℝ) ^ s1 := by
      rw [hs1_def, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ (5 / 4 : ℝ) ^ 4) k1
    have hs1_lo : 1125 * R ≤ (5 / 4 : ℝ) ^ s1 := hK1_lo.trans (hk1_bounds.1.trans h54_pow)
    have hη_lo' : 1 / (225 * R) ≤ η := by rwa [hR_def, hLξ_def]
    have hη5_lo : 1 / (1125 * R) ≤ η / 5 := by
      have : 1 / (1125 * R) = (1 / (225 * R)) / 5 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hη_lo' (by norm_num)
    have hprod : (1125 * R) * (1 / (1125 * R)) ≤ (5 / 4 : ℝ) ^ s1 * (η / 5) :=
      mul_le_mul hs1_lo hη5_lo (by positivity) (by positivity)
    have h1 : (1125 * R) * (1 / (1125 * R)) = 1 := mul_one_div_cancel (by positivity)
    linarith only [hprod, h1]
  have hstop_prod : (4 * β) ^ (n * M) * ((1 / 3) * (1 / 2) ^ (2 ^ s2)) ≤ ξ / 16 := by
    have hβ_pow : 4 * β ≤ (2 : ℝ) ^ (2 * KLβ + 2) := by
      have h1 : 2 + β ≤ (4 : ℝ) ^ KLβ := by
        rw [hKLβ_def, hLβ_def]
        have := exp_le_four_pow (Real.log (2 + β))
        rwa [Real.exp_log (by positivity)] at this
      have h2 : (4 : ℝ) ^ KLβ = (2 : ℝ) ^ (2 * KLβ) := by
        calc (4 : ℝ) ^ KLβ = ((2 : ℝ) ^ 2) ^ KLβ := by norm_num
          _ = (2 : ℝ) ^ (2 * KLβ) := by rw [← pow_mul]
      have h3 : (2 : ℝ) ^ (2 * KLβ + 2) = 4 * (2 : ℝ) ^ (2 * KLβ) := by
        rw [pow_add]; ring
      linarith only [h1, h2, h3]
    have h4β_nM : (4 * β) ^ (n * M) ≤ (2 : ℝ) ^ (n * M * (2 * KLβ + 2)) := by
      calc (4 * β) ^ (n * M)
        _ ≤ ((2 : ℝ) ^ (2 * KLβ + 2)) ^ (n * M) :=
            pow_le_pow_left₀ (by positivity) hβ_pow (n * M)
        _ = (2 : ℝ) ^ (n * M * (2 * KLβ + 2)) := by rw [← pow_mul, mul_comm]
    have hξ_pow : 16 / ξ ≤ (2 : ℝ) ^ (2 * KLξ + 4) := by
      have h1 : 2 + 1 / ξ ≤ (4 : ℝ) ^ KLξ := by
        rw [hKLξ_def, hLξ_def]
        have := exp_le_four_pow (Real.log (2 + 1 / ξ))
        rwa [Real.exp_log (by positivity)] at this
      have h2 : (4 : ℝ) ^ KLξ = (2 : ℝ) ^ (2 * KLξ) := by
        calc (4 : ℝ) ^ KLξ = ((2 : ℝ) ^ 2) ^ KLξ := by norm_num
          _ = (2 : ℝ) ^ (2 * KLξ) := by rw [← pow_mul]
      have h3 : (2 : ℝ) ^ (2 * KLξ + 4) = 16 * (2 : ℝ) ^ (2 * KLξ) := by
        rw [pow_add]; ring
      have h4 : 16 / ξ = 16 * (1 / ξ) := by ring
      linarith only [h1, h2, h3, h4]
    have hN2_le_s2 : N2 ≤ 2 ^ s2 := by
      rw [hs2_def]
      exact (Nat.lt_pow_succ_log_self one_lt_two N2).le
    have h2N2 : (4 * β) ^ (n * M) * (16 / ξ) ≤ (2 : ℝ) ^ (2 ^ s2) := by
      calc (4 * β) ^ (n * M) * (16 / ξ)
        _ ≤ (2 : ℝ) ^ (n * M * (2 * KLβ + 2)) * (2 : ℝ) ^ (2 * KLξ + 4) :=
            mul_le_mul h4β_nM hξ_pow (by positivity) (by positivity)
        _ = (2 : ℝ) ^ N2 := by rw [hN2_def, ← pow_add, ← add_assoc]
        _ ≤ (2 : ℝ) ^ (2 ^ s2) := pow_le_pow_right₀ (by norm_num) hN2_le_s2
    have h12_eq : (1 / 2 : ℝ) ^ (2 ^ s2) = 1 / (2 : ℝ) ^ (2 ^ s2) := one_div_pow 2 (2 ^ s2)
    rw [h12_eq]
    have hdiv : (4 * β) ^ (n * M) / (2 : ℝ) ^ (2 ^ s2) ≤ ξ / 16 := by
      rw [div_le_iff₀ (by positivity)]
      have h' := mul_le_mul_of_nonneg_right h2N2 (by positivity : 0 ≤ ξ / 16)
      have h'' : (16 / ξ) * (ξ / 16) = 1 := by field_simp
      rw [mul_assoc, h'', mul_one, mul_comm ((2 : ℝ) ^ (2 ^ s2))] at h'
      exact h'
    calc (4 * β) ^ (n * M) * ((1 / 3) * (1 / (2 : ℝ) ^ (2 ^ s2)))
      _ = (1 / 3) * ((4 * β) ^ (n * M) / (2 : ℝ) ^ (2 ^ s2)) := by ring
      _ ≤ 1 * (ξ / 16) := mul_le_mul (by norm_num) hdiv (by positivity) zero_le_one
      _ = ξ / 16 := one_mul _
  have hdeg_bound : ((M * n + 3 ^ (s1 + s2) * (4 * l) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 130 * β * (Real.log (2 + β) + Real.log (2 + 1 / ξ)) ^ 15 := by
    rw [← hLβ_def, ← hLξ_def, ← hL_def]
    have hcast : ((M * n + 3 ^ (s1 + s2) * (4 * l) : ℕ) : ℝ) =
        (M : ℝ) * (n : ℝ) + (3 : ℝ) ^ s1 * (3 : ℝ) ^ s2 * (4 * (l : ℝ)) := by
      rw [pow_add]; push_cast; ring
    rw [hcast]
    have hR_le_3L : R ≤ 3 * L := by linarith only [hR_def, hL_def, hLβ_ge1, hLξ_ge1]
    have hKR_le : (KR : ℝ) ≤ 4 * L := by
      have h1 : (KR : ℝ) ≤ R + 1 := by
        rw [hKR_def]; exact (Nat.ceil_lt_add_one hR_pos.le).le
      linarith only [h1, hR_le_3L, hL_ge2]
    have hM_le : (M : ℝ) ≤ 8 * L := by
      have h1 : (Nat.ceil (2 * R + 1) : ℝ) ≤ (2 * R + 1) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have h2 : (M : ℝ) = (Nat.ceil (2 * R + 1) : ℝ) + 1 := by rw [hM_def]; push_cast; rfl
      linarith only [h1, h2, hR_le_3L, hL_ge2]
    have hn_le : (n : ℝ) ≤ 33 * L := by
      have h1 : (n : ℝ) = 3 * (M : ℝ) + 2 + 2 * (KR : ℝ) := by rw [hn_def]; push_cast; ring
      linarith only [h1, hM_le, hKR_le, hL_ge2]
    have hMn_le : (M : ℝ) * (n : ℝ) ≤ (2 : ℝ) ^ 9 * L ^ 2 := by
      calc (M : ℝ) * (n : ℝ)
        _ ≤ (8 * L) * (33 * L) := mul_le_mul hM_le hn_le (by positivity) (by positivity)
        _ = 264 * L ^ 2 := by ring
        _ ≤ (2 : ℝ) ^ 9 * L ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L)
    have hK1_le : (K1 : ℝ) ≤ (2 : ℝ) ^ 12 * L := by
      have h1 : (K1 : ℝ) ≤ 1125 * R + 1 := by
        rw [hK1_def]; exact (Nat.ceil_lt_add_one (by positivity)).le
      linarith only [h1, hR_le_3L, hL_ge2]
    have h2k1_le : (2 : ℝ) ^ k1 ≤ (2 : ℝ) ^ 14 * L := by
      have h1 := hk1_bounds.2
      linarith only [h1, hK1_le]
    have h3s1_le : (3 : ℝ) ^ s1 ≤ (2 : ℝ) ^ 98 * L ^ 7 := by
      rw [hs1_def, pow_mul]
      have h81 : (3 : ℝ) ^ 4 ≤ (2 : ℝ) ^ 7 := by norm_num
      calc ((3 : ℝ) ^ 4) ^ k1
        _ ≤ ((2 : ℝ) ^ 7) ^ k1 := pow_le_pow_left₀ (by norm_num) h81 k1
        _ = ((2 : ℝ) ^ k1) ^ 7 := by rw [← pow_mul, mul_comm, pow_mul]
        _ ≤ ((2 : ℝ) ^ 14 * L) ^ 7 := pow_le_pow_left₀ (by positivity) h2k1_le 7
        _ = (2 : ℝ) ^ 98 * L ^ 7 := by ring
    have hKLβ_le : (KLβ : ℝ) ≤ 2 * L := by
      have h1 : (KLβ : ℝ) ≤ Lβ + 1 := by
        rw [hKLβ_def]; exact (Nat.ceil_lt_add_one hLβ_pos.le).le
      linarith only [h1, hL_def, hLξ_ge1]
    have hKLξ_le : (KLξ : ℝ) ≤ 2 * L := by
      have h1 : (KLξ : ℝ) ≤ Lξ + 1 := by
        rw [hKLξ_def]; exact (Nat.ceil_lt_add_one hLξ_pos.le).le
      linarith only [h1, hL_def, hLβ_ge1]
    have hL1 : 1 ≤ L := by linarith only [hL_ge2]
    have hL1_le_L3 : L ≤ L ^ 3 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by omega)
    have hN2_le : (N2 : ℝ) ≤ (2 : ℝ) ^ 12 * L ^ 3 := by
      have hN2_cast : (N2 : ℝ) = (n : ℝ) * (M : ℝ) * (2 * (KLβ : ℝ) + 2) + (2 * (KLξ : ℝ) + 4) := by
        rw [hN2_def]; push_cast; ring
      rw [hN2_cast]
      have h1 : (n : ℝ) * (M : ℝ) ≤ (2 : ℝ) ^ 9 * L ^ 2 := by rw [mul_comm]; exact hMn_le
      have h2 : 2 * (KLβ : ℝ) + 2 ≤ 5 * L := by linarith only [hKLβ_le, hL_ge2]
      have h3 : (n : ℝ) * (M : ℝ) * (2 * (KLβ : ℝ) + 2) ≤ 2560 * L ^ 3 := by
        calc (n : ℝ) * (M : ℝ) * (2 * (KLβ : ℝ) + 2)
          _ ≤ ((2 : ℝ) ^ 9 * L ^ 2) * (5 * L) := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 2560 * L ^ 3 := by ring
      have h4 : 2 * (KLξ : ℝ) + 4 ≤ 6 * L ^ 3 := by
        calc 2 * (KLξ : ℝ) + 4 ≤ 6 * L := by linarith only [hKLξ_le, hL_ge2]
          _ ≤ 6 * L ^ 3 := mul_le_mul_of_nonneg_left hL1_le_L3 (by norm_num)
      calc (n : ℝ) * (M : ℝ) * (2 * (KLβ : ℝ) + 2) + (2 * (KLξ : ℝ) + 4)
        _ ≤ 2560 * L ^ 3 + 6 * L ^ 3 := add_le_add h3 h4
        _ = 2566 * L ^ 3 := by ring
        _ ≤ (2 : ℝ) ^ 12 * L ^ 3 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hN2_ge1 : 1 ≤ N2 := by omega
    have h2s2_le : (2 : ℝ) ^ s2 ≤ (2 : ℝ) ^ 14 * L ^ 3 := by
      have h1 : (2 : ℝ) ^ s2 ≤ 2 * (N2 : ℝ) := by
        rw [hs2_def]; exact (nat_log_bounds hN2_ge1).2
      linarith only [h1, hN2_le]
    have h3s2_le : (3 : ℝ) ^ s2 ≤ (2 : ℝ) ^ 28 * L ^ 6 := by
      have h34 : (3 : ℝ) ≤ (2 : ℝ) ^ 2 := by norm_num
      calc (3 : ℝ) ^ s2
        _ ≤ ((2 : ℝ) ^ 2) ^ s2 := pow_le_pow_left₀ (by norm_num) h34 s2
        _ = ((2 : ℝ) ^ s2) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
        _ ≤ ((2 : ℝ) ^ 14 * L ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) h2s2_le 2
        _ = (2 : ℝ) ^ 28 * L ^ 6 := by ring
    have hW_deg : (3 : ℝ) ^ s1 * (3 : ℝ) ^ s2 * (4 * (l : ℝ)) ≤
        (2 : ℝ) ^ 129 * β * L ^ 13 := by
      have h1 : (3 : ℝ) ^ s1 * (3 : ℝ) ^ s2 ≤ ((2 : ℝ) ^ 98 * L ^ 7) * ((2 : ℝ) ^ 28 * L ^ 6) :=
        mul_le_mul h3s1_le h3s2_le (by positivity) (by positivity)
      have h2 : 4 * (l : ℝ) ≤ 8 * β := by linarith only [hl_le]
      have h3 : ((3 : ℝ) ^ s1 * (3 : ℝ) ^ s2) * (4 * (l : ℝ)) ≤
          (((2 : ℝ) ^ 98 * L ^ 7) * ((2 : ℝ) ^ 28 * L ^ 6)) * (8 * β) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      have h4 : (((2 : ℝ) ^ 98 * L ^ 7) * ((2 : ℝ) ^ 28 * L ^ 6)) * (8 * β) =
          (2 : ℝ) ^ 129 * β * L ^ 13 := by ring
      exact h3.trans_eq h4
    have hL2_le_L15 : L ^ 2 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by omega)
    have hL13_le_L15 : L ^ 13 ≤ L ^ 15 := pow_le_pow_right₀ hL1 (by omega)
    have hMn_le2 : (M : ℝ) * (n : ℝ) ≤ (2 : ℝ) ^ 9 * β * L ^ 15 := by
      calc (M : ℝ) * (n : ℝ)
        _ ≤ (2 : ℝ) ^ 9 * L ^ 2 := hMn_le
        _ ≤ (2 : ℝ) ^ 9 * L ^ 15 := mul_le_mul_of_nonneg_left hL2_le_L15 (by norm_num)
        _ = (2 : ℝ) ^ 9 * 1 * L ^ 15 := by ring
        _ ≤ (2 : ℝ) ^ 9 * β * L ^ 15 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ1 (by norm_num)) (by positivity)
    have hW_deg2 : (3 : ℝ) ^ s1 * (3 : ℝ) ^ s2 * (4 * (l : ℝ)) ≤
        (2 : ℝ) ^ 129 * β * L ^ 15 :=
      hW_deg.trans (mul_le_mul_of_nonneg_left hL13_le_L15 (by positivity))
    calc (M : ℝ) * (n : ℝ) + (3 : ℝ) ^ s1 * (3 : ℝ) ^ s2 * (4 * (l : ℝ))
      _ ≤ (2 : ℝ) ^ 9 * β * L ^ 15 + (2 : ℝ) ^ 129 * β * L ^ 15 := add_le_add hMn_le2 hW_deg2
      _ = ((2 : ℝ) ^ 9 + (2 : ℝ) ^ 129) * (β * L ^ 15) := by ring
      _ ≤ (2 : ℝ) ^ 130 * (β * L ^ 15) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ 130 * β * L ^ 15 := by ring
  exact ⟨M, KR, n, s1, s2, hM_ge1, hn_def, hM_lo, h8ξ_expR', h1_4KR, hs1_amp, hstop_prod, hdeg_bound⟩

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ ξ β : ℝ, 0 < ξ → ξ ≤ 1 / 6 → 1 ≤ β →
      ∃ P : Polynomial ℝ,
        (∀ x ∈ Set.Icc (-1 : ℝ) 0, |P.eval x - Real.exp (2 * β * x) / 4| ≤ ξ) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) ∧
        (P.natDegree : ℝ) ≤ C * β * (Real.log (2 + β) + Real.log (2 + 1 / ξ)) ^ c := by
  refine ⟨(2 : ℝ) ^ 130, by positivity, 15, ?_⟩
  intro ξ β hξ0 hξ1 hβ1
  have h1_ξ : 6 ≤ 1 / ξ := by rw [le_div_iff₀ hξ0]; linarith only [hξ1]
  have hLξ_ge1 : 1 ≤ Real.log (2 + 1 / ξ) := by
    have hexp1 : Real.exp 1 ≤ 2 + 1 / ξ := by linarith only [Real.exp_one_lt_d9, h1_ξ]
    have h := Real.log_le_log (Real.exp_pos 1) hexp1
    rwa [Real.log_exp] at h
  have hR4 : 4 ≤ Real.log (2 + 1 / ξ) + 3 := by linarith only [hLξ_ge1]
  obtain ⟨x0, r1, r2, η, l, hx0_lo, hx0_hi, hr1_pos, hr12, hr2_le,
    hx0_r1, hx0_sub_r1, hx0_r2, hx0_sub_r2, hl_le, hl2_δ0, hη_eq, hη_lo, hη_le⟩ :=
    window_params_exist hβ1 hR4
  have hη_pos : 0 < η := lt_of_lt_of_le (by positivity) hη_lo
  obtain ⟨M, KR, n, s1, s2, hM_ge1, hn_eq, hM_lo, h8ξ_expR, h1_4KR, hs1_amp, hstop_prod, hdeg_bound⟩ :=
    degree_and_exp_bounds hξ0 hξ1 hβ1 hl_le hη_lo
  obtain ⟨hu0_Icc, hu0_stop, hu0_pass⟩ :=
    u0Bump_properties l hx0_lo hx0_hi hr1_pos hr12 hr2_le hl2_δ0 hη_eq hη_pos hη_le
  have hW_Icc : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η)).eval x ∧
      (iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η)).eval x ≤ 1 := by
    intro x hx
    rw [eval_iterHPoly]
    exact iter_hCubic_mem_Icc (s1 + s2) (hu0_Icc x hx).1 (hu0_Icc x hx).2
  have hW_stop : ∀ x ∈ Set.Icc (-1 : ℝ) 1, r2 ≤ |x - x0| →
      (iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η)).eval x ≤ (1 / 3) * (1 / 2) ^ (2 ^ s2) := by
    intro x hx hrx
    rw [eval_iterHPoly]
    have hmin : min (1 / 3 : ℝ) (η / 5) = η / 5 := min_eq_right (by linarith)
    refine iter_hCubic_stopband s1 s2 (hu0_Icc x hx).1 (hu0_Icc x hx).2
      (by positivity) ?_ hs1_amp
    rw [hmin]
    exact hu0_stop x hx hrx
  have hW_pass : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |x - x0| ≤ r1 →
      |(iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η)).eval x - 1| ≤
        (1 / 3) * (1 / 2) ^ (2 ^ s2) := by
    intro x hx hrx
    rw [eval_iterHPoly]
    have hsym := iter_hCubic_symm (s1 + s2) ((u0BumpPoly l x0 r2 η).eval x)
    have h01 := iter_hCubic_mem_Icc (s1 + s2) (hu0_Icc x hx).1 (hu0_Icc x hx).2
    have habs : |hCubic^[s1 + s2] ((u0BumpPoly l x0 r2 η).eval x) - 1| =
        hCubic^[s1 + s2] (1 - (u0BumpPoly l x0 r2 η).eval x) := by
      rw [hsym, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs]
    have hmin : min (1 / 3 : ℝ) (η / 5) = η / 5 := min_eq_right (by linarith)
    refine iter_hCubic_stopband s1 s2 (by linarith [(hu0_Icc x hx).2])
      (by linarith [(hu0_Icc x hx).1]) (by positivity) ?_ hs1_amp
    rw [hmin]
    linarith [hu0_pass x hrx]
  have hE_active : ∀ x : ℝ, |x - x0| ≤ r2 →
      |(EApproxPoly n M β).eval x - Real.exp (2 * β * x) / 4| ≤ ξ / 32 := by
    intro x hrx
    obtain ⟨hx_lo, hx_hi⟩ := abs_le.mp hrx
    have h2βx_lo : -(2 * min (Real.log (2 + 1 / ξ) + 3) β + 1 / 4) ≤ 2 * β * x := by
      have h2 : -(2 * min (Real.log (2 + 1 / ξ) + 3) β + 1 / 4) / (2 * β) ≤ x := by linarith
      have h3 := (div_le_iff₀ (by positivity : 0 < 2 * β)).mp h2
      linarith
    have h2βx_hi : 2 * β * x ≤ 1 / 4 := by
      have h2 : x ≤ 1 / (8 * β) := by linarith
      have h3 := (le_div_iff₀ (by positivity : 0 < 8 * β)).mp h2
      linarith
    have hR0_le : min (Real.log (2 + 1 / ξ) + 3) β ≤ Real.log (2 + 1 / ξ) + 3 :=
      min_le_left _ _
    have hy : |2 * β * x / (M : ℝ)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < M), div_le_one (by positivity)]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    exact (EApproxPoly_active_bound hM_ge1 hn_eq hy).trans h1_4KR
  have hE_global : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(EApproxPoly n M β).eval x| ≤ (4 * β) ^ (n * M) :=
    fun x hx => EApproxPoly_global_bound n M hM_ge1 hβ1 hx
  have hBE1 : (1 : ℝ) ≤ (4 * β) ^ (n * M) := one_le_pow₀ (by linarith)
  have heval := product_eval_bounds (EApproxPoly n M β)
    (iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η))
    hξ0 hξ1 hβ1 hx0_r1 hx0_sub_r1 hx0_r2 hr12 h8ξ_expR
    hBE1 (by positivity) hstop_prod hW_Icc hW_stop hW_pass hE_active hE_global
  refine ⟨EApproxPoly n M β * iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η),
    heval.1, heval.2, ?_⟩
  have hdeg_mul : (EApproxPoly n M β * iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η)).natDegree ≤
      M * n + 3 ^ (s1 + s2) * (4 * l) := by
    refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_EApproxPoly_le n M β) ?_)
    refine (natDegree_iterHPoly_le (s1 + s2) (u0BumpPoly l x0 r2 η)).trans ?_
    exact Nat.mul_le_mul_left _ (natDegree_u0BumpPoly_le l x0 r2 η)
  have hdeg_cast : ((EApproxPoly n M β * iterHPoly (s1 + s2) (u0BumpPoly l x0 r2 η)).natDegree : ℝ) ≤
      ((M * n + 3 ^ (s1 + s2) * (4 * l) : ℕ) : ℝ) := by exact_mod_cast hdeg_mul
  exact hdeg_cast.trans hdeg_bound
