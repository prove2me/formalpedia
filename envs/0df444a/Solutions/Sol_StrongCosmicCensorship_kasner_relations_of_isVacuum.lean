-- Prove2me | solution 1 for StrongCosmicCensorship.kasner_relations_of_isVacuum
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:36:46.868026+00:00
-- url     : https://prove2.me/submissions/42e247e4-bd9f-40be-91a2-60f5380ca3c3

import Mathlib
import Definitions.Def_scc_coordinate_framework

open StrongCosmicCensorship

theorem W7a_StrongCosmicCensorship_pd_prod (A B : ℝ → ℝ) (i j k : Fin 4) (x : Coords)
    (hA : DifferentiableAt ℝ A (x i)) (hB : DifferentiableAt ℝ B (x j)) :
    pd k (fun y => A (y i) * B (y j)) x =
      (if k = i then deriv A (x i) * B (x j) else 0) +
      (if k = j then A (x i) * deriv B (x j) else 0) := by
  have h1 : HasFDerivAt (fun y : Coords => A (y i))
      (deriv A (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x :=
    hA.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply i x)
  have h2 : HasFDerivAt (fun y : Coords => B (y j))
      (deriv B (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j) x :=
    hB.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply j x)
  have h3 : HasFDerivAt (fun y : Coords => A (y i) * B (y j)) _ x := h1.mul h2
  unfold pd dir
  rw [h3.fderiv]
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [hi, hj, Pi.single_apply, eq_comm] <;> ring

theorem W7a_StrongCosmicCensorship_ginv_diag (h : Fin 4 → Coords → ℝ) (x : Coords)
    (hx : ∀ i, h i x ≠ 0) :
    ginv (fun y => Matrix.diagonal (fun i => h i y)) x = Matrix.diagonal (fun i => (h i x)⁻¹) := by
  unfold ginv
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; exact inv_mul_cancel₀ (hx i)

theorem W7a_StrongCosmicCensorship_chr_diag (h : Fin 4 → Coords → ℝ) (x : Coords)
    (hx : ∀ i, h i x ≠ 0) (a b c : Fin 4) :
    christoffel (fun y => Matrix.diagonal (fun i => h i y)) a b c x =
      (1 / 2 : ℝ) * (h a x)⁻¹ * ((if a = c then pd b (h a) x else 0)
        + (if b = a then pd c (h b) x else 0)
        - (if b = c then pd a (h b) x else 0)) := by
  have hinv := W7a_StrongCosmicCensorship_ginv_diag h x hx
  have hp : ∀ (i j k : Fin 4), pd k (fun y => if i = j then h i y else 0) x
      = if i = j then pd k (h i) x else 0 := by
    intro i j k
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, pd]
  unfold christoffel
  simp only [hinv, Matrix.diagonal_apply, hp, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring

/-! ## Schwarzschild -/

noncomputable def W7a_StrongCosmicCensorship_sA (M : ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun r => -(1 - 2 * M / r), fun r => (1 - 2 * M / r)⁻¹, fun r => r ^ 2, fun r => r ^ 2]

noncomputable def W7a_StrongCosmicCensorship_sA' (M : ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun r => -(2 * M / r ^ 2), fun r => -(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2,
    fun r => 2 * r, fun r => 2 * r]

noncomputable def W7a_StrongCosmicCensorship_sB : Fin 4 → ℝ → ℝ :=
  ![fun _ => 1, fun _ => 1, fun _ => 1, fun t => Real.sin t ^ 2]

noncomputable def W7a_StrongCosmicCensorship_sB' : Fin 4 → ℝ → ℝ :=
  ![fun _ => 0, fun _ => 0, fun _ => 0, fun t => 2 * Real.sin t * Real.cos t]

theorem W7a_StrongCosmicCensorship_schw_eq (M : ℝ) :
    schwarzschild M = fun y => Matrix.diagonal (fun i =>
      W7a_StrongCosmicCensorship_sA M i (y 1) * W7a_StrongCosmicCensorship_sB i (y 2)) := by
  funext y
  show Matrix.diagonal _ = Matrix.diagonal _
  congr 1; funext i
  fin_cases i <;> simp [W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sB,
    schwarzschildLapse]

theorem W7a_StrongCosmicCensorship_lapse_hd (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun r => 1 - 2 * M / r) (2 * M / r ^ 2) r := by
  have := ((hasDerivAt_inv hr).const_mul (2 * M)).const_sub 1
  have e : (fun r => 1 - 2 * M / r) = fun x => 1 - 2 * M * x⁻¹ := by funext y; ring
  rw [e]
  exact this.congr_deriv (by ring)

theorem W7a_StrongCosmicCensorship_lapse_ne (M r : ℝ) (hr : r ≠ 0) (hf : r - 2 * M ≠ 0) :
    1 - 2 * M / r ≠ 0 := by
  rw [one_sub_div hr]; exact div_ne_zero hf hr

theorem W7a_StrongCosmicCensorship_hdA (M r : ℝ) (hr : r ≠ 0) (hf : r - 2 * M ≠ 0)
    (i : Fin 4) :
    HasDerivAt (W7a_StrongCosmicCensorship_sA M i) (W7a_StrongCosmicCensorship_sA' M i r) r := by
  have h0 := W7a_StrongCosmicCensorship_lapse_hd M r hr
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    exact (hasDerivAt_pow 2 r).congr_deriv (by norm_num)
  fin_cases i
  · exact h0.neg
  · exact h0.inv (W7a_StrongCosmicCensorship_lapse_ne M r hr hf)
  · exact h2
  · exact h2

theorem W7a_StrongCosmicCensorship_hdB (t : ℝ) (i : Fin 4) :
    HasDerivAt (W7a_StrongCosmicCensorship_sB i) (W7a_StrongCosmicCensorship_sB' i t) t := by
  fin_cases i
  · exact hasDerivAt_const t (1 : ℝ)
  · exact hasDerivAt_const t (1 : ℝ)
  · exact hasDerivAt_const t (1 : ℝ)
  · show HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t
    exact ((Real.hasDerivAt_sin t).pow 2).congr_deriv (by norm_num)

theorem W7a_StrongCosmicCensorship_sne (M : ℝ) (y : Coords) (hr : y 1 ≠ 0)
    (hf : y 1 - 2 * M ≠ 0) (hs : Real.sin (y 2) ≠ 0) (i : Fin 4) :
    W7a_StrongCosmicCensorship_sA M i (y 1) * W7a_StrongCosmicCensorship_sB i (y 2) ≠ 0 := by
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (y 1) hr hf
  have hl' : 2 * M / y 1 - 1 ≠ 0 := by intro h; apply hl; linarith
  fin_cases i <;>
    simp [W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sB, hr, hs, hl, hl']

noncomputable def W7a_StrongCosmicCensorship_GA (M : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let O : ℝ → ℝ := fun _ => 1
  let a1 : ℝ → ℝ := fun r => M / (r * (r - 2 * M))
  let a2 : ℝ → ℝ := fun r => M * (r - 2 * M) / r ^ 3
  let a3 : ℝ → ℝ := fun r => -(M / (r * (r - 2 * M)))
  let a4 : ℝ → ℝ := fun r => -(r - 2 * M)
  let a5 : ℝ → ℝ := fun r => 1 / r
  ![![![Z, a1, Z, Z], ![a1, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![a2, Z, Z, Z], ![Z, a3, Z, Z], ![Z, Z, a4, Z], ![Z, Z, Z, a4]],
    ![![Z, Z, Z, Z], ![Z, Z, a5, Z], ![Z, a5, Z, Z], ![Z, Z, Z, O]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, a5], ![Z, Z, Z, O], ![Z, a5, O, Z]]]

noncomputable def W7a_StrongCosmicCensorship_GA' (M : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let a1 : ℝ → ℝ := fun r => -(M * (2 * r - 2 * M)) / (r * (r - 2 * M)) ^ 2
  let a2 : ℝ → ℝ := fun r => M * (6 * M - 2 * r) / r ^ 4
  let a3 : ℝ → ℝ := fun r => M * (2 * r - 2 * M) / (r * (r - 2 * M)) ^ 2
  let a4 : ℝ → ℝ := fun _ => -1
  let a5 : ℝ → ℝ := fun r => -1 / r ^ 2
  ![![![Z, a1, Z, Z], ![a1, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![a2, Z, Z, Z], ![Z, a3, Z, Z], ![Z, Z, a4, Z], ![Z, Z, Z, a4]],
    ![![Z, Z, Z, Z], ![Z, Z, a5, Z], ![Z, a5, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, a5], ![Z, Z, Z, Z], ![Z, a5, Z, Z]]]

noncomputable def W7a_StrongCosmicCensorship_GB : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let O : ℝ → ℝ := fun _ => 1
  let b1 : ℝ → ℝ := fun t => Real.sin t ^ 2
  let b2 : ℝ → ℝ := fun t => -(Real.sin t * Real.cos t)
  let b3 : ℝ → ℝ := fun t => Real.cos t / Real.sin t
  ![![![Z, O, Z, Z], ![O, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![O, Z, Z, Z], ![Z, O, Z, Z], ![Z, Z, O, Z], ![Z, Z, Z, b1]],
    ![![Z, Z, Z, Z], ![Z, Z, O, Z], ![Z, O, Z, Z], ![Z, Z, Z, b2]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, O], ![Z, Z, Z, b3], ![Z, O, b3, Z]]]

noncomputable def W7a_StrongCosmicCensorship_GB' : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let b1 : ℝ → ℝ := fun t => 2 * Real.sin t * Real.cos t
  let b2 : ℝ → ℝ := fun t => Real.sin t ^ 2 - Real.cos t ^ 2
  let b3 : ℝ → ℝ := fun t => -1 / Real.sin t ^ 2
  ![![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, b1]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, b2]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, b3], ![Z, Z, b3, Z]]]

theorem W7a_StrongCosmicCensorship_GA_hd (M r : ℝ) (hr : r ≠ 0) (hf : r - 2 * M ≠ 0)
    (a b c : Fin 4) :
    HasDerivAt (W7a_StrongCosmicCensorship_GA M a b c) (W7a_StrongCosmicCensorship_GA' M a b c r) r := by
  have hq : HasDerivAt (fun r => r * (r - 2 * M)) (1 * (r - 2 * M) + r * 1) r :=
    (hasDerivAt_id' r).mul ((hasDerivAt_id' r).sub_const (2 * M))
  have hq0 : r * (r - 2 * M) ≠ 0 := mul_ne_zero hr hf
  have h1 : HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * r - 2 * M)) / (r * (r - 2 * M)) ^ 2) r :=
    ((hasDerivAt_const r M).div hq hq0).congr_deriv (by ring)
  have h3 : HasDerivAt (fun r => -(M / (r * (r - 2 * M))))
      (M * (2 * r - 2 * M) / (r * (r - 2 * M)) ^ 2) r :=
    h1.neg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun r => M * (r - 2 * M) / r ^ 3) (M * (6 * M - 2 * r) / r ^ 4) r := by
    have hc : HasDerivAt (fun r : ℝ => r ^ 3) (3 * r ^ 2) r := by
      exact (hasDerivAt_pow 3 r).congr_deriv (by norm_num)
    exact ((((hasDerivAt_id' r).sub_const (2 * M)).const_mul M).div hc
      (pow_ne_zero 3 hr)).congr_deriv (by field_simp; ring)
  have h4 : HasDerivAt (fun r => -(r - 2 * M)) (-1) r :=
    ((hasDerivAt_id' r).sub_const (2 * M)).neg
  have h5 : HasDerivAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) r :=
    ((hasDerivAt_const r (1 : ℝ)).div (hasDerivAt_id' r) hr).congr_deriv (by ring)
  have hZ : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 r := hasDerivAt_const r 0
  have hO : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const r 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact hZ | exact hO | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

theorem W7a_StrongCosmicCensorship_GB_hd (t : ℝ) (hs : Real.sin t ≠ 0) (a b c : Fin 4) :
    HasDerivAt (W7a_StrongCosmicCensorship_GB a b c) (W7a_StrongCosmicCensorship_GB' a b c t) t := by
  have h1 : HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t := by
    exact ((Real.hasDerivAt_sin t).pow 2).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun t => -(Real.sin t * Real.cos t)) (Real.sin t ^ 2 - Real.cos t ^ 2) t :=
    ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).neg.congr_deriv (by ring)
  have h3 : HasDerivAt (fun t => Real.cos t / Real.sin t) (-1 / Real.sin t ^ 2) t :=
    ((Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs).congr_deriv (by
      rw [div_eq_div_iff (pow_ne_zero 2 hs) (pow_ne_zero 2 hs)]
      nlinarith [Real.sin_sq_add_cos_sq t])
  have hZ : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have hO : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact hZ | exact hO | exact h1 | exact h2 | exact h3

theorem W7a_StrongCosmicCensorship_chr_tab (M : ℝ) (y : Coords) (hr : y 1 ≠ 0)
    (hf : y 1 - 2 * M ≠ 0) (hs : Real.sin (y 2) ≠ 0) (a b c : Fin 4) :
    christoffel (schwarzschild M) a b c y =
      W7a_StrongCosmicCensorship_GA M a b c (y 1) * W7a_StrongCosmicCensorship_GB a b c (y 2) := by
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (y 1) hr hf
  have n1 : 2 * M - y 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - y 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : y 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + y 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + y 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -y 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -y 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  have hp : ∀ i k, pd k (fun z => W7a_StrongCosmicCensorship_sA M i (z 1) * W7a_StrongCosmicCensorship_sB i (z 2)) y =
      (if k = 1 then W7a_StrongCosmicCensorship_sA' M i (y 1) * W7a_StrongCosmicCensorship_sB i (y 2) else 0)
        + (if k = 2 then W7a_StrongCosmicCensorship_sA M i (y 1) * W7a_StrongCosmicCensorship_sB' i (y 2) else 0) := by
    intro i k
    rw [W7a_StrongCosmicCensorship_pd_prod _ _ 1 2 k y
      (W7a_StrongCosmicCensorship_hdA M (y 1) hr hf i).differentiableAt
      (W7a_StrongCosmicCensorship_hdB (y 2) i).differentiableAt,
      (W7a_StrongCosmicCensorship_hdA M (y 1) hr hf i).deriv,
      (W7a_StrongCosmicCensorship_hdB (y 2) i).deriv]
  rw [W7a_StrongCosmicCensorship_schw_eq M, W7a_StrongCosmicCensorship_chr_diag
    (fun i z => W7a_StrongCosmicCensorship_sA M i (z 1) * W7a_StrongCosmicCensorship_sB i (z 2)) y
    (W7a_StrongCosmicCensorship_sne M y hr hf hs)]
  simp only [hp]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sA',
      W7a_StrongCosmicCensorship_sB, W7a_StrongCosmicCensorship_sB',
      W7a_StrongCosmicCensorship_GA, W7a_StrongCosmicCensorship_GB] <;>
    field_simp <;> ring

theorem W7a_StrongCosmicCensorship_pd_chr (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (a b c k : Fin 4) :
    pd k (christoffel (schwarzschild M) a b c) x =
      (if k = 1 then W7a_StrongCosmicCensorship_GA' M a b c (x 1) * W7a_StrongCosmicCensorship_GB a b c (x 2) else 0) +
      (if k = 2 then W7a_StrongCosmicCensorship_GA M a b c (x 1) * W7a_StrongCosmicCensorship_GB' a b c (x 2) else 0) := by
  have hΩ : IsOpen {y : Coords | y 1 ≠ 0 ∧ y 1 - 2 * M ≠ 0 ∧ Real.sin (y 2) ≠ 0} := by
    refine (isOpen_ne_fun (continuous_apply 1) continuous_const).inter
      ((isOpen_ne_fun ((continuous_apply 1).sub continuous_const) continuous_const).inter
        (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const))
  have hev : (christoffel (schwarzschild M) a b c) =ᶠ[nhds x]
      (fun y => W7a_StrongCosmicCensorship_GA M a b c (y 1) * W7a_StrongCosmicCensorship_GB a b c (y 2)) :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds ⟨hr, hf, hs⟩)
      (fun y hy => W7a_StrongCosmicCensorship_chr_tab M y hy.1 hy.2.1 hy.2.2 a b c)
  have hA := W7a_StrongCosmicCensorship_GA_hd M (x 1) hr hf a b c
  have hB := W7a_StrongCosmicCensorship_GB_hd (x 2) hs a b c
  have := W7a_StrongCosmicCensorship_pd_prod _ _ 1 2 k x hA.differentiableAt hB.differentiableAt
  rw [hA.deriv, hB.deriv] at this
  rw [← this]
  unfold pd
  rw [hev.fderiv_eq]

theorem W7a_StrongCosmicCensorship_ricci_zero (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (b d : Fin 4) :
    ricci (schwarzschild M) b d x = 0 := by
  have hc4 : Real.cos (x 2) ^ 4 = (1 - Real.sin (x 2) ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -x 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  unfold ricci riemann
  simp only [W7a_StrongCosmicCensorship_pd_chr M x hr hf hs,
    W7a_StrongCosmicCensorship_chr_tab M x hr hf hs]
  fin_cases b <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_GA, W7a_StrongCosmicCensorship_GB,
      W7a_StrongCosmicCensorship_GA', W7a_StrongCosmicCensorship_GB'] <;>
    field_simp <;> ring_nf <;> (try simp only [Real.cos_sq', hc4]) <;> ring_nf

theorem W7a_StrongCosmicCensorship_schwarzschild_isVacuum (M : ℝ) (hM : 0 < M) :
    IsVacuum (schwarzschildExterior M) (schwarzschild M) := by
  intro x hx b d
  obtain ⟨h1, h2, h3⟩ := hx
  have hr : x 1 ≠ 0 := by intro h; linarith
  have hf : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h2 h3).ne'
  exact W7a_StrongCosmicCensorship_ricci_zero M x hr hf hs b d

theorem W7a_StrongCosmicCensorship_schwarzschild_isVacuum_interior (M : ℝ) (hM : 0 < M) :
    IsVacuum (schwarzschildInterior M) (schwarzschild M) := by
  intro x hx b d
  obtain ⟨h0, h1, h2, h3⟩ := hx
  have hr : x 1 ≠ 0 := by intro h; linarith
  have hf : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h2 h3).ne'
  exact W7a_StrongCosmicCensorship_ricci_zero M x hr hf hs b d

/-! ## Kasner -/

theorem W7a_StrongCosmicCensorship_pd_one (A : ℝ → ℝ) (k : Fin 4) (x : Coords)
    (hA : DifferentiableAt ℝ A (x 0)) :
    pd k (fun y => A (y 0)) x = if k = 0 then deriv A (x 0) else 0 := by
  have h1 : HasFDerivAt (fun y : Coords => A (y 0))
      (deriv A (x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) x :=
    hA.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply 0 x)
  unfold pd dir
  rw [h1.fderiv]
  by_cases hk : k = 0 <;> simp [hk, Pi.single_apply, eq_comm]

noncomputable def W7a_StrongCosmicCensorship_kA (p : Fin 3 → ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun _ => -1, fun t => t ^ (2 * p 0), fun t => t ^ (2 * p 1), fun t => t ^ (2 * p 2)]

noncomputable def W7a_StrongCosmicCensorship_kA' (p : Fin 3 → ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun _ => 0, fun t => 2 * p 0 * (t ^ (2 * p 0) / t), fun t => 2 * p 1 * (t ^ (2 * p 1) / t),
    fun t => 2 * p 2 * (t ^ (2 * p 2) / t)]

theorem W7a_StrongCosmicCensorship_kasner_eq (p : Fin 3 → ℝ) :
    kasner p = fun y => Matrix.diagonal (fun i => W7a_StrongCosmicCensorship_kA p i (y 0)) := by
  funext y
  show Matrix.diagonal _ = Matrix.diagonal _
  congr 1; funext i
  fin_cases i <;> simp [W7a_StrongCosmicCensorship_kA, Real.rpow_eq_pow]

theorem W7a_StrongCosmicCensorship_hw (p : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t) (k : Fin 3) :
    HasDerivAt (fun t : ℝ => t ^ (2 * p k)) (2 * p k * (t ^ (2 * p k) / t)) t :=
  (Real.hasDerivAt_rpow_const (p := 2 * p k) (Or.inl ht.ne')).congr_deriv
    (by rw [Real.rpow_sub_one ht.ne'])

theorem W7a_StrongCosmicCensorship_hdK (p : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t) (i : Fin 4) :
    HasDerivAt (W7a_StrongCosmicCensorship_kA p i) (W7a_StrongCosmicCensorship_kA' p i t) t := by
  fin_cases i
  · exact hasDerivAt_const t (-1 : ℝ)
  · exact W7a_StrongCosmicCensorship_hw p t ht 0
  · exact W7a_StrongCosmicCensorship_hw p t ht 1
  · exact W7a_StrongCosmicCensorship_hw p t ht 2

noncomputable def W7a_StrongCosmicCensorship_KG (p : Fin 3 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let c0 : ℝ → ℝ := fun t => p 0 * (t ^ (2 * p 0) / t)
  let c1 : ℝ → ℝ := fun t => p 1 * (t ^ (2 * p 1) / t)
  let c2 : ℝ → ℝ := fun t => p 2 * (t ^ (2 * p 2) / t)
  let q0 : ℝ → ℝ := fun t => p 0 / t
  let q1 : ℝ → ℝ := fun t => p 1 / t
  let q2 : ℝ → ℝ := fun t => p 2 / t
  ![![![Z, Z, Z, Z], ![Z, c0, Z, Z], ![Z, Z, c1, Z], ![Z, Z, Z, c2]],
    ![![Z, q0, Z, Z], ![q0, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, q1, Z], ![Z, Z, Z, Z], ![q1, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, Z, q2], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![q2, Z, Z, Z]]]

noncomputable def W7a_StrongCosmicCensorship_KG' (p : Fin 3 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let c0 : ℝ → ℝ := fun t => p 0 * (2 * p 0 - 1) * t ^ (2 * p 0) / t ^ 2
  let c1 : ℝ → ℝ := fun t => p 1 * (2 * p 1 - 1) * t ^ (2 * p 1) / t ^ 2
  let c2 : ℝ → ℝ := fun t => p 2 * (2 * p 2 - 1) * t ^ (2 * p 2) / t ^ 2
  let q0 : ℝ → ℝ := fun t => -p 0 / t ^ 2
  let q1 : ℝ → ℝ := fun t => -p 1 / t ^ 2
  let q2 : ℝ → ℝ := fun t => -p 2 / t ^ 2
  ![![![Z, Z, Z, Z], ![Z, c0, Z, Z], ![Z, Z, c1, Z], ![Z, Z, Z, c2]],
    ![![Z, q0, Z, Z], ![q0, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, q1, Z], ![Z, Z, Z, Z], ![q1, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, Z, q2], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![q2, Z, Z, Z]]]

theorem W7a_StrongCosmicCensorship_KG_hd (p : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t) (a b c : Fin 4) :
    HasDerivAt (W7a_StrongCosmicCensorship_KG p a b c) (W7a_StrongCosmicCensorship_KG' p a b c t) t := by
  have hc : ∀ k : Fin 3, HasDerivAt (fun t : ℝ => p k * (t ^ (2 * p k) / t))
      (p k * (2 * p k - 1) * t ^ (2 * p k) / t ^ 2) t := fun k =>
    (((W7a_StrongCosmicCensorship_hw p t ht k).div (hasDerivAt_id' t) ht.ne').const_mul
      (p k)).congr_deriv (by field_simp)
  have hq : ∀ k : Fin 3, HasDerivAt (fun t : ℝ => p k / t) (-p k / t ^ 2) t := fun k =>
    ((hasDerivAt_const t (p k)).div (hasDerivAt_id' t) ht.ne').congr_deriv (by ring)
  have hZ : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact hZ | exact hc 0 | exact hc 1 | exact hc 2 | exact hq 0 | exact hq 1 | exact hq 2

theorem W7a_StrongCosmicCensorship_kchr_tab (p : Fin 3 → ℝ) (y : Coords) (ht : 0 < y 0)
    (a b c : Fin 4) :
    christoffel (kasner p) a b c y = W7a_StrongCosmicCensorship_KG p a b c (y 0) := by
  have w0 : y 0 ^ (2 * p 0) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have w1 : y 0 ^ (2 * p 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have w2 : y 0 ^ (2 * p 2) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have ht' : y 0 ≠ 0 := ht.ne'
  have hne : ∀ i, W7a_StrongCosmicCensorship_kA p i (y 0) ≠ 0 := by
    intro i; fin_cases i <;> simp [W7a_StrongCosmicCensorship_kA, w0, w1, w2]
  have hp : ∀ i k, pd k (fun z => W7a_StrongCosmicCensorship_kA p i (z 0)) y =
      if k = 0 then W7a_StrongCosmicCensorship_kA' p i (y 0) else 0 := by
    intro i k
    rw [W7a_StrongCosmicCensorship_pd_one _ k y
      (W7a_StrongCosmicCensorship_hdK p (y 0) ht i).differentiableAt,
      (W7a_StrongCosmicCensorship_hdK p (y 0) ht i).deriv]
  rw [W7a_StrongCosmicCensorship_kasner_eq p, W7a_StrongCosmicCensorship_chr_diag
    (fun i z => W7a_StrongCosmicCensorship_kA p i (z 0)) y hne]
  simp only [hp]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [W7a_StrongCosmicCensorship_kA, W7a_StrongCosmicCensorship_kA',
      W7a_StrongCosmicCensorship_KG] <;>
    field_simp <;> ring

theorem W7a_StrongCosmicCensorship_kpd_chr (p : Fin 3 → ℝ) (x : Coords) (ht : 0 < x 0)
    (a b c k : Fin 4) :
    pd k (christoffel (kasner p) a b c) x =
      if k = 0 then W7a_StrongCosmicCensorship_KG' p a b c (x 0) else 0 := by
  have hev : (christoffel (kasner p) a b c) =ᶠ[nhds x]
      (fun y => W7a_StrongCosmicCensorship_KG p a b c (y 0)) :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds ht)
      (fun y hy => W7a_StrongCosmicCensorship_kchr_tab p y hy a b c)
  have hA := W7a_StrongCosmicCensorship_KG_hd p (x 0) ht a b c
  have := W7a_StrongCosmicCensorship_pd_one _ k x hA.differentiableAt
  rw [hA.deriv] at this
  rw [← this]
  unfold pd
  rw [hev.fderiv_eq]

noncomputable def W7a_StrongCosmicCensorship_KR (p : Fin 3 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![(p 0 + p 1 + p 2 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)) / t ^ 2,
    p 0 * (p 0 + p 1 + p 2 - 1) * t ^ (2 * p 0) / t ^ 2,
    p 1 * (p 0 + p 1 + p 2 - 1) * t ^ (2 * p 1) / t ^ 2,
    p 2 * (p 0 + p 1 + p 2 - 1) * t ^ (2 * p 2) / t ^ 2]

theorem W7a_StrongCosmicCensorship_kricci (p : Fin 3 → ℝ) (x : Coords) (ht : 0 < x 0)
    (b d : Fin 4) :
    ricci (kasner p) b d x = if b = d then W7a_StrongCosmicCensorship_KR p (x 0) b else 0 := by
  have w0 : x 0 ^ (2 * p 0) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have w1 : x 0 ^ (2 * p 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have w2 : x 0 ^ (2 * p 2) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have ht' : x 0 ≠ 0 := ht.ne'
  unfold ricci riemann
  simp only [W7a_StrongCosmicCensorship_kpd_chr p x ht, W7a_StrongCosmicCensorship_kchr_tab p x ht]
  fin_cases b <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_KG, W7a_StrongCosmicCensorship_KG',
      W7a_StrongCosmicCensorship_KR] <;>
    field_simp <;> ring

theorem W7a_StrongCosmicCensorship_kasner_isVacuum (p : Fin 3 → ℝ) (hp : KasnerRelations p) :
    IsVacuum kasnerRegion (kasner p) := by
  intro x hx b d
  obtain ⟨h1, h2⟩ := hp
  simp only [Fin.sum_univ_three] at h1 h2
  rw [W7a_StrongCosmicCensorship_kricci p x hx]
  split_ifs
  · fin_cases b <;> simp [W7a_StrongCosmicCensorship_KR, h1, h2]
  · rfl

theorem solution (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hvac : IsVacuum kasnerRegion (kasner p)) :
    KasnerRelations p := by
  have hx : (![1, 0, 0, 0] : Coords) ∈ kasnerRegion := by
    show (0 : ℝ) < ![(1 : ℝ), 0, 0, 0] 0; norm_num
  have e0 := hvac _ hx 0 0
  have e1 := hvac _ hx 1 1
  rw [W7a_StrongCosmicCensorship_kricci p _ (by simpa using hx)] at e0 e1
  simp [W7a_StrongCosmicCensorship_KR] at e0 e1
  have hp0 := hp 0
  have hs : p 0 + p 1 + p 2 = 1 := by
    rcases e1 with h | h
    · linarith
    · linarith
  refine ⟨by simp [Fin.sum_univ_three]; linarith, by simp [Fin.sum_univ_three]; nlinarith⟩

/-! ## Kretschmann scalar of Schwarzschild -/

noncomputable def W7a_StrongCosmicCensorship_kap (M r : ℝ) (a b : Fin 4) : ℝ :=
  if a = b then 0 else
    if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 2 * M / r ^ 3
    else -(M / r ^ 3)

set_option maxHeartbeats 2000000 in
theorem W7a_StrongCosmicCensorship_riem_val0 (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (b c d : Fin 4) :
    riemann (schwarzschild M) 0 b c d x =
      W7a_StrongCosmicCensorship_kap M (x 1) 0 b *
        ((if (0 : Fin 4) = c ∧ b = d then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)
          - (if (0 : Fin 4) = d ∧ b = c then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)) := by
  have hc4 : Real.cos (x 2) ^ 4 = (1 - Real.sin (x 2) ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (x 1) hr hf
  have hl' : 2 * M / x 1 - 1 ≠ 0 := by intro h; apply hl; linarith
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -x 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  unfold riemann
  simp only [W7a_StrongCosmicCensorship_pd_chr M x hr hf hs,
    W7a_StrongCosmicCensorship_chr_tab M x hr hf hs]
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_GA, W7a_StrongCosmicCensorship_GB,
      W7a_StrongCosmicCensorship_GA', W7a_StrongCosmicCensorship_GB', W7a_StrongCosmicCensorship_kap,
      W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sB] <;>
    field_simp <;> ring_nf <;> (try simp only [Real.cos_sq', hc4]) <;> ring_nf

set_option maxHeartbeats 2000000 in
theorem W7a_StrongCosmicCensorship_riem_val1 (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (b c d : Fin 4) :
    riemann (schwarzschild M) 1 b c d x =
      W7a_StrongCosmicCensorship_kap M (x 1) 1 b *
        ((if (1 : Fin 4) = c ∧ b = d then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)
          - (if (1 : Fin 4) = d ∧ b = c then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)) := by
  have hc4 : Real.cos (x 2) ^ 4 = (1 - Real.sin (x 2) ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (x 1) hr hf
  have hl' : 2 * M / x 1 - 1 ≠ 0 := by intro h; apply hl; linarith
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -x 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  unfold riemann
  simp only [W7a_StrongCosmicCensorship_pd_chr M x hr hf hs,
    W7a_StrongCosmicCensorship_chr_tab M x hr hf hs]
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_GA, W7a_StrongCosmicCensorship_GB,
      W7a_StrongCosmicCensorship_GA', W7a_StrongCosmicCensorship_GB', W7a_StrongCosmicCensorship_kap,
      W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sB] <;>
    field_simp <;> ring_nf <;> (try simp only [Real.cos_sq', hc4]) <;> ring_nf

set_option maxHeartbeats 2000000 in
theorem W7a_StrongCosmicCensorship_riem_val2 (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (b c d : Fin 4) :
    riemann (schwarzschild M) 2 b c d x =
      W7a_StrongCosmicCensorship_kap M (x 1) 2 b *
        ((if (2 : Fin 4) = c ∧ b = d then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)
          - (if (2 : Fin 4) = d ∧ b = c then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)) := by
  have hc4 : Real.cos (x 2) ^ 4 = (1 - Real.sin (x 2) ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (x 1) hr hf
  have hl' : 2 * M / x 1 - 1 ≠ 0 := by intro h; apply hl; linarith
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -x 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  unfold riemann
  simp only [W7a_StrongCosmicCensorship_pd_chr M x hr hf hs,
    W7a_StrongCosmicCensorship_chr_tab M x hr hf hs]
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_GA, W7a_StrongCosmicCensorship_GB,
      W7a_StrongCosmicCensorship_GA', W7a_StrongCosmicCensorship_GB', W7a_StrongCosmicCensorship_kap,
      W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sB] <;>
    field_simp <;> ring_nf <;> (try simp only [Real.cos_sq', hc4]) <;> ring_nf

set_option maxHeartbeats 2000000 in
theorem W7a_StrongCosmicCensorship_riem_val3 (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (b c d : Fin 4) :
    riemann (schwarzschild M) 3 b c d x =
      W7a_StrongCosmicCensorship_kap M (x 1) 3 b *
        ((if (3 : Fin 4) = c ∧ b = d then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)
          - (if (3 : Fin 4) = d ∧ b = c then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)) := by
  have hc4 : Real.cos (x 2) ^ 4 = (1 - Real.sin (x 2) ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (x 1) hr hf
  have hl' : 2 * M / x 1 - 1 ≠ 0 := by intro h; apply hl; linarith
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -x 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  unfold riemann
  simp only [W7a_StrongCosmicCensorship_pd_chr M x hr hf hs,
    W7a_StrongCosmicCensorship_chr_tab M x hr hf hs]
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_GA, W7a_StrongCosmicCensorship_GB,
      W7a_StrongCosmicCensorship_GA', W7a_StrongCosmicCensorship_GB', W7a_StrongCosmicCensorship_kap,
      W7a_StrongCosmicCensorship_sA, W7a_StrongCosmicCensorship_sB] <;>
    field_simp <;> ring_nf <;> (try simp only [Real.cos_sq', hc4]) <;> ring_nf

theorem W7a_StrongCosmicCensorship_riem_val (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (a b c d : Fin 4) :
    riemann (schwarzschild M) a b c d x =
      W7a_StrongCosmicCensorship_kap M (x 1) a b *
        ((if a = c ∧ b = d then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)
          - (if a = d ∧ b = c then W7a_StrongCosmicCensorship_sA M b (x 1) * W7a_StrongCosmicCensorship_sB b (x 2) else 0)) := by
  fin_cases a
  · exact W7a_StrongCosmicCensorship_riem_val0 M x hr hf hs b c d
  · exact W7a_StrongCosmicCensorship_riem_val1 M x hr hf hs b c d
  · exact W7a_StrongCosmicCensorship_riem_val2 M x hr hf hs b c d
  · exact W7a_StrongCosmicCensorship_riem_val3 M x hr hf hs b c d

theorem W7a_StrongCosmicCensorship_kretsch_val (M : ℝ) (x : Coords) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    kretschmann (schwarzschild M) x = 48 * M ^ 2 / (x 1) ^ 6 := by
  have hg : ginv (schwarzschild M) x =
      Matrix.diagonal (fun i => (W7a_StrongCosmicCensorship_sA M i (x 1) * W7a_StrongCosmicCensorship_sB i (x 2))⁻¹) := by
    rw [W7a_StrongCosmicCensorship_schw_eq]
    exact W7a_StrongCosmicCensorship_ginv_diag _ x (W7a_StrongCosmicCensorship_sne M x hr hf hs)
  have hgx : schwarzschild M x =
      Matrix.diagonal (fun i => W7a_StrongCosmicCensorship_sA M i (x 1) * W7a_StrongCosmicCensorship_sB i (x 2)) := by
    rw [W7a_StrongCosmicCensorship_schw_eq]
  have hRL : ∀ a b c d, riemannLower (schwarzschild M) a b c d x =
      W7a_StrongCosmicCensorship_sA M a (x 1) * W7a_StrongCosmicCensorship_sB a (x 2) *
        riemann (schwarzschild M) a b c d x := by
    intro a b c d
    unfold riemannLower
    rw [hgx]
    simp [Matrix.diagonal_apply]
  have key : ∀ a b c d : Fin 4,
      (∑ a' : Fin 4, ∑ b' : Fin 4, ∑ c' : Fin 4, ∑ d' : Fin 4,
        riemannLower (schwarzschild M) a b c d x * riemannLower (schwarzschild M) a' b' c' d' x *
          ginv (schwarzschild M) x a a' * ginv (schwarzschild M) x b b' *
          ginv (schwarzschild M) x c c' * ginv (schwarzschild M) x d d') =
      riemannLower (schwarzschild M) a b c d x * riemannLower (schwarzschild M) a b c d x *
        ginv (schwarzschild M) x a a * ginv (schwarzschild M) x b b *
        ginv (schwarzschild M) x c c * ginv (schwarzschild M) x d d := by
    intro a b c d
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single d]
          · intro d' _ hd; simp [hg, Matrix.diagonal_apply_ne _ (Ne.symm hd)]
          · simp
        · intro c' _ hc; simp [hg, Matrix.diagonal_apply_ne _ (Ne.symm hc)]
        · simp
      · intro b' _ hb; simp [hg, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
      · simp
    · intro a' _ ha; simp [hg, Matrix.diagonal_apply_ne _ (Ne.symm ha)]
    · simp
  have hl := W7a_StrongCosmicCensorship_lapse_ne M (x 1) hr hf
  have hl' : 2 * M / x 1 - 1 ≠ 0 := by intro h; apply hl; linarith
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  unfold kretschmann
  simp only [key]
  simp only [hRL, W7a_StrongCosmicCensorship_riem_val M x hr hf hs, hg]
  simp [Fin.sum_univ_four, W7a_StrongCosmicCensorship_kap, W7a_StrongCosmicCensorship_sA,
    W7a_StrongCosmicCensorship_sB]
  field_simp
  ring

theorem W7a_StrongCosmicCensorship_schwarzschild_kretschmann (M : ℝ) (hM : 0 < M)
    (x : Coords) (hx : x ∈ schwarzschildInterior M) :
    kretschmann (schwarzschild M) x = 48 * M ^ 2 / (x 1) ^ 6 := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  have hr : x 1 ≠ 0 := by intro h; linarith
  have hf : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h2 h3).ne'
  exact W7a_StrongCosmicCensorship_kretsch_val M x hr hf hs

theorem W7a_StrongCosmicCensorship_schwarzschild_kretschmann_unbounded (M : ℝ) (hM : 0 < M) (C : ℝ) :
    ∃ x ∈ schwarzschildInterior M, C < kretschmann (schwarzschild M) x := by
  set r : ℝ := min (min M 1) (48 * M ^ 2 / (2 * (|C| + 1))) / 2 with hr
  have hC : 0 < |C| + 1 := by positivity
  have hq : 0 < 48 * M ^ 2 / (2 * (|C| + 1)) := by positivity
  have hr0 : 0 < r := by
    rw [hr]; apply div_pos _ two_pos
    exact lt_min (lt_min hM one_pos) hq
  have hm : min (min M 1) (48 * M ^ 2 / (2 * (|C| + 1))) ≤ min M 1 := min_le_left _ _
  have hm2 : min (min M 1) (48 * M ^ 2 / (2 * (|C| + 1))) ≤ 48 * M ^ 2 / (2 * (|C| + 1)) :=
    min_le_right _ _
  have hmM : min M 1 ≤ M := min_le_left _ _
  have hm1 : min M 1 ≤ 1 := min_le_right _ _
  have hrM : r < 2 * M := by rw [hr]; linarith
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hrC : r ≤ 48 * M ^ 2 / (2 * (|C| + 1)) := by rw [hr]; linarith
  have hx : (![0, r, Real.pi / 2, 0] : Coords) ∈ schwarzschildInterior M := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> first | exact hr0 | exact hrM | positivity | linarith [Real.pi_pos]
  refine ⟨_, hx, ?_⟩
  rw [W7a_StrongCosmicCensorship_schwarzschild_kretschmann M hM _ hx]
  show C < 48 * M ^ 2 / r ^ 6
  have h6 : r ^ 6 ≤ r := by
    calc r ^ 6 ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
      _ = r := pow_one r
  have hCr : C * r < 48 * M ^ 2 := by
    have h1 : r * (2 * (|C| + 1)) ≤ 48 * M ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hrC; linarith
    nlinarith [le_abs_self C, abs_nonneg C]
  have hA : C < 48 * M ^ 2 / r := by rw [lt_div_iff₀ hr0]; linarith
  have hB : 48 * M ^ 2 / r ≤ 48 * M ^ 2 / r ^ 6 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h6
  linarith
