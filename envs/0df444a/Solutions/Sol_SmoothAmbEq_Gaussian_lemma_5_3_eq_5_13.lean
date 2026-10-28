-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.lemma_5_3_eq_5_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:32:02.002785+00:00
-- url     : https://prove2.me/submissions/10763aa0-b338-4a47-82cc-a99ae82c34fc

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_lemma_C_2

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SAL53

open SmoothAmbEq.Gaussian


open SmoothAmbEq.Gaussian

lemma den_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by
  have := M.hσ; have := M.hσ₀; positivity

lemma zeta_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.ζ t := by
  unfold Model.ζ
  have := den_pos M ht; have := M.hσ; have := M.hσ₀; positivity

lemma zeta_continuousOn (M : Model) : ContinuousOn M.ζ (Ici 0) := by
  unfold Model.ζ
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht; exact (den_pos M ht).ne'

/-- FTC for `t ↦ ∫_t^b f` within `[a, b]` for `f` continuous on `[a, b]`. -/
lemma ftc_left {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun u => ∫ s in u..b, f s) (-f t) (Icc a b) t := by
  set g : ℝ → ℝ := fun s => f (max a (min s b)) with hg_def
  have hgc : Continuous g := by
    apply hf.comp_continuous (by fun_prop)
    intro s; exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hgf : EqOn g f (Icc a b) := by
    intro s hs; simp [hg_def, min_eq_left hs.2, max_eq_right hs.1]
  have hd : HasDerivAt (fun u => ∫ s in u..b, g s) (-g t) t :=
    intervalIntegral.integral_hasDerivAt_left (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  rw [← hgf ht]
  refine hd.hasDerivWithinAt.congr_of_mem ?_ ht
  intro u hu
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hu.2] at hs
  exact (hgf ⟨hu.1.trans hs.1, hs.2⟩).symm

/-- A solution of the linear equation `d' = K d` on `[0, T]` (derivatives within `[0, T]`)
with `d(T) = 0` vanishes on `[0, T]`. -/
lemma linear_ode_zero {d K : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hK : ContinuousOn K (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt d (K t * d t) (Icc 0 T) t) (hdT : d T = 0) :
    ∀ t ∈ Icc 0 T, d t = 0 := by
  set E : ℝ → ℝ := fun t => Real.exp (∫ s in t..T, K s) with hE_def
  have hE : ∀ t ∈ Icc 0 T, HasDerivWithinAt E (E t * (-K t)) (Icc 0 T) t := by
    intro t ht
    exact (ftc_left hT hK ht).exp
  have hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => d t * E t) 0 (Icc 0 T) t := by
    intro t ht
    exact ((hd t ht).mul (hE t ht)).congr_deriv (by ring)
  have hcont : ContinuousOn (fun t => d t * E t) (Icc 0 T) :=
    fun t ht => (hf t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun x hx =>
    (hf x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)))
  intro t ht
  have h1 := hconst t ht
  have h2 := hconst T ⟨hT, le_rfl⟩
  simp only [hdT, zero_mul] at h2
  have hEpos : 0 < E t := Real.exp_pos _
  have : d t * E t = 0 := by rw [h1, ← h2]
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h hEpos.ne'


/-- (5.11). -/
lemma m45 (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) :
    ∀ t ∈ Icc 0 M.T,
      c.m₄ t = -M.r * c.m₁ t - M.r * c.m₂ t ∧ c.m₅ t = -M.r * c.m₂ t - M.r * c.m₃ t := by
  have hc' := hc
  obtain ⟨hD, h1, h2, h3, h4, h5, h6, h1T, h2T, h3T, h4T, h5T, h6T⟩ := hc'
  have hT := M.hT
  have hσ := M.hσ
  have hσ2 : M.σ ^ 2 ≠ 0 := by positivity
  have hk : M.k ≠ 0 := M.hk.ne'
  have zpos : ∀ t ∈ Icc 0 M.T, 0 < M.ζ t := fun t ht => zeta_pos M ht.1
  have cz : ContinuousOn M.ζ (Icc 0 M.T) :=
    (zeta_continuousOn M).mono (fun t ht => ht.1)
  have czi : ContinuousOn (fun t => (M.ζ t)⁻¹) (Icc 0 M.T) :=
    cz.inv₀ (fun t ht => (zpos t ht).ne')
  have c1 : ContinuousOn c.m₁ (Icc 0 M.T) := fun t ht => (h1 t ht).continuousWithinAt
  have c2 : ContinuousOn c.m₂ (Icc 0 M.T) := fun t ht => (h2 t ht).continuousWithinAt
  have c3 : ContinuousOn c.m₃ (Icc 0 M.T) := fun t ht => (h3 t ht).continuousWithinAt
  have cA2 : ContinuousOn (fun s => a₂ M s (c.m₂ s) (c.m₃ s)) (Icc 0 M.T) := by
    unfold a₂
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (hD t ht).ne'
  have key : ∀ t ∈ Icc 0 M.T, a₂ M t (c.m₂ t) (c.m₃ t) * (c.m₂ t + c.m₃ t)
      = a₁ M t (c.m₂ t) (c.m₃ t) - M.ζ t * c.m₂ t - 1 := by
    intro t ht
    have hd := (hD t ht).ne'
    unfold a₁ a₂
    have hinv : ((M.ζ t)⁻¹ - M.α * c.m₃ t) * ((M.ζ t)⁻¹ - M.α * c.m₃ t)⁻¹ = 1 :=
      mul_inv_cancel₀ hd
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(1 + M.ζ t * c.m₂ t)) * hinv
  -- (5.11), second identity: m₅ = -r m₂ - r m₃
  have hm5 : ∀ t ∈ Icc 0 M.T, c.m₅ t = -M.r * c.m₂ t - M.r * c.m₃ t := by
    have := linear_ode_zero (d := fun t => c.m₅ t - (-M.r * c.m₂ t - M.r * c.m₃ t))
      (K := fun t => (1 + M.ζ t * c.m₂ t) * a₂ M t (c.m₂ t) (c.m₃ t) / M.σ ^ 2) hT.le
      (by fun_prop)
      (by
        intro t ht
        refine ((h5 t ht).sub (((h2 t ht).const_mul (-M.r)).sub
          ((h3 t ht).const_mul M.r))).congr_deriv ?_
        linear_combination (-(1 + M.ζ t * c.m₂ t) * M.r / M.σ ^ 2) * key t ht)
      (by simp [h5T, h2T, h3T])
    intro t ht
    have h : c.m₅ t - (-M.r * c.m₂ t - M.r * c.m₃ t) = 0 := this t ht
    linarith
  -- (5.11), first identity: m₄ = -r m₁ - r m₂
  have hm4 : ∀ t ∈ Icc 0 M.T, c.m₄ t = -M.r * c.m₁ t - M.r * c.m₂ t := by
    have := linear_ode_zero (d := fun t => c.m₄ t - (-M.r * c.m₁ t - M.r * c.m₂ t))
      (K := fun t => M.ζ t / M.σ ^ 2) hT.le (by fun_prop)
      (by
        intro t ht
        refine ((h4 t ht).sub (((h1 t ht).const_mul (-M.r)).sub
          ((h2 t ht).const_mul M.r))).congr_deriv ?_
        linear_combination
          (-(a₁ M t (c.m₂ t) (c.m₃ t) * a₂ M t (c.m₂ t) (c.m₃ t)) / M.σ ^ 2) * hm5 t ht
          + (M.r * a₁ M t (c.m₂ t) (c.m₃ t) / M.σ ^ 2) * key t ht)
      (by simp [h4T, h1T, h2T])
    intro t ht
    have h : c.m₄ t - (-M.r * c.m₁ t - M.r * c.m₂ t) = 0 := this t ht
    linarith
  exact fun t ht => ⟨hm4 t ht, hm5 t ht⟩

/-- (5.14): `𝒜^{z,π*} g^z = 0`. -/
lemma gen_star_zero (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) (z t : ℝ)
    (ht : t ∈ Icc 0 M.T) (x β : ℝ) :
    gen M z (piStar M c t x β) (gz M c z) t x β = 0 := by
  have hc' := hc
  obtain ⟨hD, h1, h2, h3, h4, h5, h6, h1T, h2T, h3T, h4T, h5T, h6T⟩ := hc'
  have hT := M.hT
  have hσ := M.hσ
  have hσ2 : M.σ ^ 2 ≠ 0 := by positivity
  have hk : M.k ≠ 0 := M.hk.ne'
  have zpos : ∀ t ∈ Icc 0 M.T, 0 < M.ζ t := fun t ht => zeta_pos M ht.1
  have cz : ContinuousOn M.ζ (Icc 0 M.T) :=
    (zeta_continuousOn M).mono (fun t ht => ht.1)
  have czi : ContinuousOn (fun t => (M.ζ t)⁻¹) (Icc 0 M.T) :=
    cz.inv₀ (fun t ht => (zpos t ht).ne')
  have c1 : ContinuousOn c.m₁ (Icc 0 M.T) := fun t ht => (h1 t ht).continuousWithinAt
  have c2 : ContinuousOn c.m₂ (Icc 0 M.T) := fun t ht => (h2 t ht).continuousWithinAt
  have c3 : ContinuousOn c.m₃ (Icc 0 M.T) := fun t ht => (h3 t ht).continuousWithinAt
  have cA2 : ContinuousOn (fun s => a₂ M s (c.m₂ s) (c.m₃ s)) (Icc 0 M.T) := by
    unfold a₂
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (hD t ht).ne'
  have key : ∀ t ∈ Icc 0 M.T, a₂ M t (c.m₂ t) (c.m₃ t) * (c.m₂ t + c.m₃ t)
      = a₁ M t (c.m₂ t) (c.m₃ t) - M.ζ t * c.m₂ t - 1 := by
    intro t ht
    have hd := (hD t ht).ne'
    unfold a₁ a₂
    have hinv : ((M.ζ t)⁻¹ - M.α * c.m₃ t) * ((M.ζ t)⁻¹ - M.α * c.m₃ t)⁻¹ = 1 :=
      mul_inv_cancel₀ hd
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(1 + M.ζ t * c.m₂ t)) * hinv
  -- (5.11), second identity: m₅ = -r m₂ - r m₃
  have hm5 : ∀ t ∈ Icc 0 M.T, c.m₅ t = -M.r * c.m₂ t - M.r * c.m₃ t := by
    have := linear_ode_zero (d := fun t => c.m₅ t - (-M.r * c.m₂ t - M.r * c.m₃ t))
      (K := fun t => (1 + M.ζ t * c.m₂ t) * a₂ M t (c.m₂ t) (c.m₃ t) / M.σ ^ 2) hT.le
      (by fun_prop)
      (by
        intro t ht
        refine ((h5 t ht).sub (((h2 t ht).const_mul (-M.r)).sub
          ((h3 t ht).const_mul M.r))).congr_deriv ?_
        linear_combination (-(1 + M.ζ t * c.m₂ t) * M.r / M.σ ^ 2) * key t ht)
      (by simp [h5T, h2T, h3T])
    intro t ht
    have h : c.m₅ t - (-M.r * c.m₂ t - M.r * c.m₃ t) = 0 := this t ht
    linarith
  -- (5.11), first identity: m₄ = -r m₁ - r m₂
  have hm4 : ∀ t ∈ Icc 0 M.T, c.m₄ t = -M.r * c.m₁ t - M.r * c.m₂ t := by
    have := linear_ode_zero (d := fun t => c.m₄ t - (-M.r * c.m₁ t - M.r * c.m₂ t))
      (K := fun t => M.ζ t / M.σ ^ 2) hT.le (by fun_prop)
      (by
        intro t ht
        refine ((h4 t ht).sub (((h1 t ht).const_mul (-M.r)).sub
          ((h2 t ht).const_mul M.r))).congr_deriv ?_
        linear_combination
          (-(a₁ M t (c.m₂ t) (c.m₃ t) * a₂ M t (c.m₂ t) (c.m₃ t)) / M.σ ^ 2) * hm5 t ht
          + (M.r * a₁ M t (c.m₂ t) (c.m₃ t) / M.σ ^ 2) * key t ht)
      (by simp [h4T, h1T, h2T])
    intro t ht
    have h : c.m₄ t - (-M.r * c.m₁ t - M.r * c.m₂ t) = 0 := this t ht
    linarith
  set E : ℝ := Real.exp (M.r * (M.T - t)) with hE
  set fb : ℝ := c.m₁ t * β + c.m₂ t * z + c.m₄ t with hfb
  -- x-derivatives
  have dx : ∀ y b : ℝ, HasDerivAt (fun y => gz M c z t y b) (gz M c z t y b * (-M.k * E)) y := by
    intro y b
    have := ((((hasDerivAt_id' y).const_mul (-M.k * E)).add_const (fz c z t b)).exp).const_mul
      (-(1 / M.k))
    refine this.congr_deriv ?_
    simp only [gz, hE]; ring
  have Dx : ∀ b : ℝ, deriv (fun y => gz M c z t y b) = fun y => gz M c z t y b * (-M.k * E) :=
    fun b => funext fun y => (dx y b).deriv
  have dxx : deriv (fun y => deriv (fun y' => gz M c z t y' β) y) x
      = gz M c z t x β * (-M.k * E) * (-M.k * E) := by
    rw [Dx β]; exact ((dx x β).mul_const _).deriv
  -- β-derivatives
  have dfz : ∀ b : ℝ, HasDerivAt (fun b => fz c z t b) (c.m₁ t * b + c.m₂ t * z + c.m₄ t) b := by
    intro b
    have := ((((((hasDerivAt_pow 2 b).const_mul (1 / 2 * c.m₁ t)).add
      (((hasDerivAt_id' b).const_mul (c.m₂ t)).mul_const z)).add_const
      (1 / 2 * c.m₃ t * z ^ 2)).add ((hasDerivAt_id' b).const_mul (c.m₄ t))).add_const
      (c.m₅ t * z)).add_const (c.m₆ t)
    refine this.congr_deriv ?_
    push_cast; ring
  have db : ∀ y b : ℝ, HasDerivAt (fun b => gz M c z t y b)
      (gz M c z t y b * (c.m₁ t * b + c.m₂ t * z + c.m₄ t)) b := by
    intro y b
    have := ((((dfz b).const_add (-M.k * E * y)).exp).const_mul (-(1 / M.k)))
    refine this.congr_deriv ?_
    simp only [gz, hE]; ring
  have Db : ∀ y : ℝ, deriv (fun b => gz M c z t y b)
      = fun b => gz M c z t y b * (c.m₁ t * b + c.m₂ t * z + c.m₄ t) :=
    fun y => funext fun b => (db y b).deriv
  have dbb : deriv (fun b => deriv (fun b' => gz M c z t x b') b) β
      = gz M c z t x β * fb * fb + gz M c z t x β * c.m₁ t := by
    rw [Db x]
    have := (db x β).mul ((((hasDerivAt_id' β).const_mul (c.m₁ t)).add_const
      (c.m₂ t * z)).add_const (c.m₄ t))
    refine this.deriv.trans ?_
    simp only [hfb]; ring
  have dxb : deriv (fun b => deriv (fun y => gz M c z t y b) x) β = gz M c z t x β * fb * (-M.k * E) := by
    have e : (fun b => deriv (fun y => gz M c z t y b) x) = fun b => gz M c z t x b * (-M.k * E) :=
      funext fun b => by rw [Dx b]
    rw [e, ((db x β).mul_const _).deriv]
  -- time derivative
  have dE : HasDerivAt (fun s => Real.exp (M.r * (M.T - s))) (E * (M.r * -1)) t := by
    have := (((hasDerivAt_id' t).const_sub M.T).const_mul M.r).exp
    simpa [hE] using this
  have dft : HasDerivWithinAt (fun s => fz c z s β)
      (1 / 2 * ((2 * M.ζ t * c.m₁ t - (a₁ M t (c.m₂ t) (c.m₃ t)) ^ 2) / M.σ ^ 2) * β ^ 2
        + (((1 + M.ζ t * c.m₂ t) * a₁ M t (c.m₂ t) (c.m₃ t) + M.ζ t * c.m₂ t) / M.σ ^ 2) * β * z
        + 1 / 2 * ((-2 * M.ζ t * c.m₂ t - M.ζ t ^ 2 * c.m₂ t ^ 2) / M.σ ^ 2) * z ^ 2
        + ((M.ζ t * c.m₄ t - a₁ M t (c.m₂ t) (c.m₃ t) * a₂ M t (c.m₂ t) (c.m₃ t) * c.m₅ t
            - M.r * M.ζ t * c.m₁ t) / M.σ ^ 2) * β
        + (((1 + M.ζ t * c.m₂ t) * a₂ M t (c.m₂ t) (c.m₃ t) * c.m₅ t
            - M.r * (1 + M.ζ t * c.m₂ t)) / M.σ ^ 2) * z
        + ((-(1 / 2) * (a₂ M t (c.m₂ t) (c.m₃ t)) ^ 2 * c.m₅ t ^ 2 + 1 / 2 * M.r ^ 2
            - 1 / 2 * M.ζ t ^ 2 * c.m₁ t - M.r * M.ζ t * c.m₄ t) / M.σ ^ 2))
      (Icc 0 M.T) t :=
    ((((((h1 t ht).const_mul (1 / 2)).mul_const (β ^ 2)).add
      (((h2 t ht).mul_const β).mul_const z)).add
      (((h3 t ht).const_mul (1 / 2)).mul_const (z ^ 2))).add
      ((h4 t ht).mul_const β)).add ((h5 t ht).mul_const z) |>.add (h6 t ht)
  have dtime := (((((dE.const_mul (-M.k)).mul_const x).hasDerivWithinAt (s := Icc 0 M.T)).add
    dft).exp).const_mul (-(1 / M.k))
  have dtw : derivWithin (fun s => gz M c z s x β) (Icc 0 M.T) t = _ :=
    dtime.derivWithin (uniqueDiffOn_Icc hT t ht)
  unfold gen
  rw [dtw, dxx, dbb, dxb, Dx β, Db x]
  -- substitute (5.11) and the key identity
  have hA1 : a₁ M t (c.m₂ t) (c.m₃ t)
      = a₂ M t (c.m₂ t) (c.m₃ t) * (c.m₂ t + c.m₃ t) + M.ζ t * c.m₂ t + 1 := by
    linarith [key t ht]
  have hEi : Real.exp (-M.r * (M.T - t)) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]; ring_nf
  have hEpos : E ≠ 0 := (Real.exp_pos _).ne'
  simp only [Pi.add_apply, gz, piStar, hEi, hfb, hm4 t ht, hm5 t ht, hA1]
  rw [← hE]
  field_simp
  ring

/-- The generator is quadratic in the action. -/
lemma gen_sub (M : Model) (c : Coeffs) (z p q t x β : ℝ) :
    gen M z p (gz M c z) t x β = gen M z q (gz M c z) t x β
      + gz M c z t x β * (p - q) * (-M.k * Real.exp (M.r * (M.T - t)) * (z - M.r)
        - M.k * Real.exp (M.r * (M.T - t)) * M.ζ t * (c.m₁ t * β + c.m₂ t * z + c.m₄ t)
        + 1 / 2 * M.σ ^ 2 * M.k ^ 2 * Real.exp (M.r * (M.T - t)) ^ 2 * (p + q)) := by
  set E : ℝ := Real.exp (M.r * (M.T - t)) with hE
  set fb : ℝ := c.m₁ t * β + c.m₂ t * z + c.m₄ t with hfb
  have dx : ∀ y b : ℝ, HasDerivAt (fun y => gz M c z t y b) (gz M c z t y b * (-M.k * E)) y := by
    intro y b
    have := ((((hasDerivAt_id' y).const_mul (-M.k * E)).add_const (fz c z t b)).exp).const_mul
      (-(1 / M.k))
    refine this.congr_deriv ?_
    simp only [gz, hE]; ring
  have Dx : ∀ b : ℝ, deriv (fun y => gz M c z t y b) = fun y => gz M c z t y b * (-M.k * E) :=
    fun b => funext fun y => (dx y b).deriv
  have dxx : deriv (fun y => deriv (fun y' => gz M c z t y' β) y) x
      = gz M c z t x β * (-M.k * E) * (-M.k * E) := by
    rw [Dx β]; exact ((dx x β).mul_const _).deriv
  have dfz : ∀ b : ℝ, HasDerivAt (fun b => fz c z t b) (c.m₁ t * b + c.m₂ t * z + c.m₄ t) b := by
    intro b
    have := ((((((hasDerivAt_pow 2 b).const_mul (1 / 2 * c.m₁ t)).add
      (((hasDerivAt_id' b).const_mul (c.m₂ t)).mul_const z)).add_const
      (1 / 2 * c.m₃ t * z ^ 2)).add ((hasDerivAt_id' b).const_mul (c.m₄ t))).add_const
      (c.m₅ t * z)).add_const (c.m₆ t)
    refine this.congr_deriv ?_
    push_cast; ring
  have db : ∀ y b : ℝ, HasDerivAt (fun b => gz M c z t y b)
      (gz M c z t y b * (c.m₁ t * b + c.m₂ t * z + c.m₄ t)) b := by
    intro y b
    have := ((((dfz b).const_add (-M.k * E * y)).exp).const_mul (-(1 / M.k)))
    refine this.congr_deriv ?_
    simp only [gz, hE]; ring
  have dxb : deriv (fun b => deriv (fun y => gz M c z t y b) x) β
      = gz M c z t x β * fb * (-M.k * E) := by
    have e : (fun b => deriv (fun y => gz M c z t y b) x) = fun b => gz M c z t x b * (-M.k * E) :=
      funext fun b => by rw [Dx b]
    rw [e, ((db x β).mul_const _).deriv]
  unfold gen
  rw [dxx, dxb, Dx β]
  ring

/-- Pointwise form of the integrand of (5.13). -/
lemma integrand_eq (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) (t : ℝ)
    (ht : t ∈ Icc 0 M.T) (x β p z : ℝ) :
    M.φ' (gz M c z t x β) * gen M z p (gz M c z) t x β =
      -(p - piStar M c t x β) *
        ((1 / M.k) ^ M.α * Real.exp (M.α * (-M.k * Real.exp (M.r * (M.T - t)) * x
          + 1 / 2 * c.m₁ t * β ^ 2 + c.m₄ t * β + c.m₆ t))) *
        (((M.k * Real.exp (M.r * (M.T - t)) * M.r
            - M.k * Real.exp (M.r * (M.T - t)) * M.ζ t * (c.m₁ t * β + c.m₄ t)
            + 1 / 2 * M.σ ^ 2 * M.k ^ 2 * Real.exp (M.r * (M.T - t)) ^ 2 * (p + piStar M c t x β))
          + (-M.k * Real.exp (M.r * (M.T - t)) - M.k * Real.exp (M.r * (M.T - t)) * M.ζ t * c.m₂ t)
            * z) *
          Real.exp (M.α * c.m₃ t / 2 * z ^ 2 + M.α * (c.m₂ t * β + c.m₅ t) * z)) := by
  have hk := M.hk
  rw [gen_sub M c z p (piStar M c t x β) t x β, gen_star_zero M c hc z t ht x β, zero_add]
  set E := Real.exp (M.r * (M.T - t)) with hE
  set Y := -M.k * E * x + fz c z t β with hY
  have hg : gz M c z t x β = -(1 / M.k * Real.exp Y) := by
    simp only [gz, hY, hE]; ring
  have hpos : 0 < 1 / M.k * Real.exp Y := by positivity
  have hφ : M.φ' (gz M c z t x β) * gz M c z t x β = -((1 / M.k * Real.exp Y) ^ M.α) := by
    unfold Model.φ'
    rw [hg, neg_neg, Real.rpow_sub_one hpos.ne']
    field_simp
  have hpow : (1 / M.k * Real.exp Y) ^ M.α = (1 / M.k) ^ M.α *
      Real.exp (M.α * (-M.k * E * x + 1 / 2 * c.m₁ t * β ^ 2 + c.m₄ t * β + c.m₆ t)) *
      Real.exp (M.α * c.m₃ t / 2 * z ^ 2 + M.α * (c.m₂ t * β + c.m₅ t) * z) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    simp only [hY, fz]; ring
  calc M.φ' (gz M c z t x β) * (gz M c z t x β * (p - piStar M c t x β) * (-M.k * E * (z - M.r)
        - M.k * E * M.ζ t * (c.m₁ t * β + c.m₂ t * z + c.m₄ t)
        + 1 / 2 * M.σ ^ 2 * M.k ^ 2 * E ^ 2 * (p + piStar M c t x β)))
      = (M.φ' (gz M c z t x β) * gz M c z t x β) * (p - piStar M c t x β) * (-M.k * E * (z - M.r)
        - M.k * E * M.ζ t * (c.m₁ t * β + c.m₂ t * z + c.m₄ t)
        + 1 / 2 * M.σ ^ 2 * M.k ^ 2 * E ^ 2 * (p + piStar M c t x β)) := by ring
    _ = _ := by rw [hφ, hpow]; ring

/-- The first-order condition defining `π*` (algebraic part). -/
lemma alg (k E σ r ζ α m₁ m₂ m₃ m₄ m₅ β p : ℝ) (hk : k ≠ 0) (hE : E ≠ 0) (hσ : σ ≠ 0)
    (hζ : ζ ≠ 0) (hD : ζ⁻¹ - α * m₃ ≠ 0) (hD' : 1 - 2 * (α * m₃ / 2) * ζ ≠ 0)
    (h4 : m₄ = -r * m₁ - r * m₂) (h5 : m₅ = -r * m₂ - r * m₃) :
    (k * E * r - k * E * ζ * (m₁ * β + m₄)
        + 1 / 2 * σ ^ 2 * k ^ 2 * E ^ 2 *
          (p + E⁻¹ / (k * σ ^ 2) * ((1 + ζ * m₂) * (ζ⁻¹ + α * m₂) / (ζ⁻¹ - α * m₃) + ζ * m₁)
            * (β - r)))
      + (-k * E - k * E * ζ * m₂) *
        ((β + α * (m₂ * β + m₅) * ζ) / (1 - 2 * (α * m₃ / 2) * ζ))
      = 1 / 2 * σ ^ 2 * k ^ 2 * E ^ 2 *
          (p - E⁻¹ / (k * σ ^ 2) * ((1 + ζ * m₂) * (ζ⁻¹ + α * m₂) / (ζ⁻¹ - α * m₃) + ζ * m₁)
            * (β - r)) := by
  have hD2 : 1 - α * m₃ * ζ ≠ 0 := by
    intro h; apply hD'; linarith
  have hD3 : 1 - ζ * α * m₃ ≠ 0 := by
    intro h; apply hD2; linarith
  have e1 : ζ⁻¹ - α * m₃ = (1 - α * m₃ * ζ) / ζ := by field_simp
  have e2 : 1 - 2 * (α * m₃ / 2) * ζ = 1 - α * m₃ * ζ := by ring
  rw [e1, e2, h4, h5]
  field_simp
  ring

/-- The expectation in (5.13) is `-K₀ (p - π*)²` with `K₀ ≥ 0`. -/
lemma value_formula (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) (t : ℝ)
    (ht : t ∈ Icc 0 M.T) (x β p : ℝ) :
    Integrable (fun z => M.φ' (gz M c z t x β) * gen M z p (gz M c z) t x β)
        (posterior M t β) ∧
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∫ z, M.φ' (gz M c z t x β) * gen M z p (gz M c z) t x β
        ∂(posterior M t β) = -K₀ * (p - piStar M c t x β) ^ 2 := by
  have hk := M.hk
  have hσ := M.hσ
  have hζ : 0 < M.ζ t := by
    unfold Model.ζ; have := M.hσ₀; have : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by
      have := ht.1; positivity
    positivity
  have hD : 0 < (M.ζ t)⁻¹ - M.α * c.m₃ t := hc.1 t ht
  obtain ⟨h4, h5⟩ := m45 M c hc t ht
  set E := Real.exp (M.r * (M.T - t)) with hE
  set pst := piStar M c t x β with hpst
  set W0 := (1 / M.k) ^ M.α * Real.exp (M.α * (-M.k * E * x
          + 1 / 2 * c.m₁ t * β ^ 2 + c.m₄ t * β + c.m₆ t)) with hW0
  have hW0 : 0 ≤ W0 := by positivity
  set c₀ := M.k * E * M.r - M.k * E * M.ζ t * (c.m₁ t * β + c.m₄ t)
            + 1 / 2 * M.σ ^ 2 * M.k ^ 2 * E ^ 2 * (p + pst) with hc₀
  set c₁ := -M.k * E - M.k * E * M.ζ t * c.m₂ t with hc₁
  set qa := M.α * c.m₃ t / 2 with hqa
  set qb := M.α * (c.m₂ t * β + c.m₅ t) with hqb
  set v : ℝ≥0 := (M.ζ t).toNNReal with hv
  have hvr : (v : ℝ) = M.ζ t := Real.coe_toNNReal _ hζ.le
  have hpost : posterior M t β = gaussianReal β v := rfl
  have hfac : 1 - 2 * qa * M.ζ t = M.ζ t * ((M.ζ t)⁻¹ - M.α * c.m₃ t) := by
    rw [hqa]; field_simp
  have hx1 : 0 < 1 - 2 * qa * M.ζ t := by rw [hfac]; positivity
  obtain ⟨hL0, hI1int, hI1⟩ := (lemma_C_2 β qa qb v).1 (by rw [hvr]; linarith)
  rw [hvr] at hL0 hI1
  set ex : ℝ → ℝ := fun z => Real.exp (qa * z ^ 2 + qb * z) with hex
  have hexm : Measurable ex := by simp only [hex]; fun_prop
  have hexint : Integrable ex (posterior M t β) := by
    refine ⟨hexm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => (Real.exp_pos _).le)]
    rw [hpost, hL0]; exact ENNReal.ofReal_lt_top
  set I0 := 1 / Real.sqrt (1 - 2 * qa * M.ζ t) *
      Real.exp ((2 * qa * β ^ 2 + 2 * β * qb + qb ^ 2 * M.ζ t) / (2 * (1 - 2 * qa * M.ζ t)))
    with hI0
  have hI0nn : 0 ≤ I0 := by positivity
  have hexI : ∫ z, ex z ∂(posterior M t β) = I0 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => (Real.exp_pos _).le)
      hexm.aestronglyMeasurable, hpost, hL0, ENNReal.toReal_ofReal hI0nn]
  have hI1' : ∫ z, z * ex z ∂(posterior M t β) =
      (β + qb * M.ζ t) / (1 - 2 * qa * M.ζ t) * I0 := by
    rw [hpost, hI1, hI0]
    have h32 : (1 - 2 * qa * M.ζ t) ^ ((3 : ℝ) / 2) =
        (1 - 2 * qa * M.ζ t) * Real.sqrt (1 - 2 * qa * M.ζ t) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx1.le (by norm_num)]
      norm_num
    rw [h32]
    have : 0 < Real.sqrt (1 - 2 * qa * M.ζ t) := Real.sqrt_pos.2 hx1
    field_simp
  have hint1 : Integrable (fun z => z * ex z) (posterior M t β) := by
    rw [hpost]; exact hI1int
  have hpt : (fun z => M.φ' (gz M c z t x β) * gen M z p (gz M c z) t x β) =
      fun z => (-(p - pst) * W0 * c₀) * ex z + (-(p - pst) * W0 * c₁) * (z * ex z) := by
    funext z
    rw [integrand_eq M c hc t ht x β p z]
    simp only [hex, hc₀, hc₁, hqa, hqb, hE, hpst]
    ring
  rw [hpt]
  refine ⟨(hexint.const_mul _).add (hint1.const_mul _), ?_⟩
  refine ⟨1 / 2 * M.σ ^ 2 * M.k ^ 2 * E ^ 2 * W0 * I0, by positivity, ?_⟩
  rw [integral_add (hexint.const_mul _) (hint1.const_mul _), integral_const_mul,
    integral_const_mul, hexI, hI1']
  have hEne : E ≠ 0 := (Real.exp_pos _).ne'
  have halg := alg M.k E M.σ M.r (M.ζ t) M.α (c.m₁ t) (c.m₂ t) (c.m₃ t) (c.m₄ t) (c.m₅ t) β p
    hk.ne' hEne hσ.ne' hζ.ne' hD.ne' (by rw [← hqa]; exact hx1.ne') h4 h5
  have hpst' : pst = E⁻¹ / (M.k * M.σ ^ 2) *
      ((1 + M.ζ t * c.m₂ t) * ((M.ζ t)⁻¹ + M.α * c.m₂ t) / ((M.ζ t)⁻¹ - M.α * c.m₃ t)
        + M.ζ t * c.m₁ t) * (β - M.r) := by
    rw [hpst, piStar, a₁, hE, ← Real.exp_neg]; ring_nf
  rw [← hpst', ← hqa, ← hqb] at halg
  have hkey : c₀ + c₁ * ((β + qb * M.ζ t) / (1 - 2 * qa * M.ζ t))
      = 1 / 2 * M.σ ^ 2 * M.k ^ 2 * E ^ 2 * (p - pst) := by
    rw [hc₀, hc₁, ← halg]
  linear_combination (-(p - pst) * W0 * I0) * hkey

end SAL53

namespace SAIto

open SmoothAmbEq.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω]

lemma filt_le_null (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (t : ℝ)
    (v : ℝ≥0) : ∀ A, MeasurableSet[shiftFiltration W t v] A → NullMeasurableSet A P := by
  have h0 : shiftFiltration W t v ≤
      (show MeasurableSpace Ω from NullMeasurableSpace.instMeasurableSpace (μ := P)) := by
    unfold shiftFiltration
    refine iSup₂_le fun u _ => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro B hB
    have hae : AEMeasurable (shiftBM W t u) P := by
      unfold shiftBM
      exact (hW.aemeasurable _).sub (hW.aemeasurable _)
    exact hae.nullMeasurable hB
  intro A hA
  exact h0 A hA

lemma aem_of_meas (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (t : ℝ)
    (v : ℝ≥0) (Z : Ω → ℝ) (hZ : Measurable[shiftFiltration W t v] Z) : AEMeasurable Z P := by
  have hgn : NullMeasurable Z P := by
    intro B hB
    exact filt_le_null P W hW t v _ (hZ hB)
  exact hgn.aemeasurable

lemma filt_mono (W : ℝ≥0 → Ω → ℝ) (t : ℝ) {v w : ℝ≥0} (h : v ≤ w) :
    shiftFiltration W t v ≤ shiftFiltration W t w := by
  unfold shiftFiltration
  exact iSup₂_le fun u hu => le_iSup₂ (f := fun u (_ : u ≤ w) =>
    MeasurableSpace.comap (shiftBM W t u) (by infer_instance)) u (hu.trans h)

lemma shiftBM_meas (W : ℝ≥0 → Ω → ℝ) (t : ℝ) {u v : ℝ≥0} (h : u ≤ v) :
    Measurable[shiftFiltration W t v] (shiftBM W t u) := by
  apply Measurable.of_comap_le
  unfold shiftFiltration
  exact le_iSup₂ (f := fun u (_ : u ≤ v) =>
    MeasurableSpace.comap (shiftBM W t u) (by infer_instance)) u h

/-- Increments after `v₀` are independent of the filtration at `v₀`. -/
lemma indep_incr (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (t : ℝ)
    {v₀ v₁ : ℝ≥0} (h : v₀ ≤ v₁) (Z : Ω → ℝ) (hZ : Measurable[shiftFiltration W t v₀] Z) :
    IndepFun Z (fun ω => shiftBM W t v₁ ω - shiftBM W t v₀ ω) P := by
  set s₀ : ℝ≥0 := t.toNNReal + v₀ with hs₀
  have hI := hW.toIsPreBrownianReal.indepFun_shift s₀
  set Fut : Ω → ℝ≥0 → ℝ := fun ω s => W (s₀ + s) ω - W s₀ ω with hFut
  set Past : Ω → Set.Iic s₀ → ℝ := fun ω s => W s ω with hPast
  -- the filtration at `v₀` is generated by the past
  have hPastm : Measurable[MeasurableSpace.comap Past inferInstance] Past :=
    Measurable.of_comap_le le_rfl
  have hle1 : shiftFiltration W t v₀ ≤ MeasurableSpace.comap Past inferInstance := by
    unfold shiftFiltration
    refine iSup₂_le fun u hu => ?_
    have hm : Measurable[MeasurableSpace.comap Past inferInstance] (shiftBM W t u) := by
      have h1 : t.toNNReal + u ∈ Set.Iic s₀ := by
        simp only [Set.mem_Iic, hs₀]; exact add_le_add_right hu _
      have h2 : t.toNNReal ∈ Set.Iic s₀ := by
        simp only [Set.mem_Iic, hs₀]; exact le_add_right le_rfl
      have e : shiftBM W t u = fun ω => (fun g : Set.Iic s₀ → ℝ => g ⟨_, h1⟩ - g ⟨_, h2⟩)
          (Past ω) := by
        funext ω; simp [shiftBM, hPast]
      rw [e]
      exact (by fun_prop : Measurable fun g : Set.Iic s₀ → ℝ => g ⟨_, h1⟩ - g ⟨_, h2⟩).comp
        hPastm
    exact hm.comap_le
  -- the increment is a function of the future
  have hFutm : Measurable[MeasurableSpace.comap Fut inferInstance] Fut :=
    Measurable.of_comap_le le_rfl
  have hle2 : MeasurableSpace.comap (fun ω => shiftBM W t v₁ ω - shiftBM W t v₀ ω) inferInstance
      ≤ MeasurableSpace.comap Fut inferInstance := by
    have hm : Measurable[MeasurableSpace.comap Fut inferInstance]
        (fun ω => shiftBM W t v₁ ω - shiftBM W t v₀ ω) := by
      have e : (fun ω => shiftBM W t v₁ ω - shiftBM W t v₀ ω) =
          fun ω => (fun g : ℝ≥0 → ℝ => g (v₁ - v₀)) (Fut ω) := by
        funext ω
        simp only [shiftBM, hFut, hs₀]
        rw [add_assoc, add_tsub_cancel_of_le h]
        ring
      rw [e]
      exact (measurable_pi_apply _).comp hFutm
    exact hm.comap_le
  rw [IndepFun_iff] at hI ⊢
  intro A B hA hB
  have hA' : MeasurableSet[MeasurableSpace.comap Past inferInstance] A :=
    hle1 _ (hZ.comap_le _ hA)
  have hB' : MeasurableSet[MeasurableSpace.comap Fut inferInstance] B := hle2 _ hB
  rw [Set.inter_comm, hI B A hB' hA', mul_comm]

lemma gauss_facts {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    AEMeasurable X P ∧ Integrable X P ∧ ∫ ω, X ω ∂P = 0 ∧
      Integrable (fun ω => X ω ^ 2) P ∧ ∫ ω, X ω ^ 2 ∂P = v := by
  have haem := hX.aemeasurable
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hint1 : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hmapeq := hX.map_eq
  refine ⟨haem, ?_, ?_, ?_, ?_⟩
  · have := (integrable_map_measure (f := X) (g := fun x : ℝ => x)
      (by fun_prop) haem).1 (by rw [hmapeq]; exact hint1)
    exact this
  · have := hX.integral_comp (f := fun x : ℝ => x) (by fun_prop)
    rw [Function.comp_def] at this
    rw [this, integral_id_gaussianReal]
  · have := (integrable_map_measure (f := X) (g := fun x : ℝ => x ^ 2)
      (by fun_prop) haem).1 (by rw [hmapeq]; exact hint2)
    exact this
  · have := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [Function.comp_def] at this
    rw [this]
    have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simpa [integral_id_gaussianReal] using hv

lemma incr_law (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (t : ℝ)
    {v₀ v₁ : ℝ≥0} (h : v₀ ≤ v₁) :
    HasLaw (fun ω => shiftBM W t v₁ ω - shiftBM W t v₀ ω) (gaussianReal 0 (v₁ - v₀)) P := by
  have := hW.hasLaw_sub (t.toNNReal + v₁) (t.toNNReal + v₀)
  have e : (fun ω => shiftBM W t v₁ ω - shiftBM W t v₀ ω) =
      W (t.toNNReal + v₁) - W (t.toNNReal + v₀) := by
    funext ω; simp only [shiftBM, Pi.sub_apply]; ring
  rw [e]
  convert this using 2
  apply NNReal.eq
  rw [coe_nndist, Real.dist_eq, NNReal.coe_sub h]
  simp only [NNReal.val_eq_coe, NNReal.coe_add]
  have : (v₀ : ℝ) ≤ v₁ := h
  rw [abs_of_nonneg (by linarith)]
  ring

/-- Itô isometry for an adapted bounded elementary integrand (discrete form). -/
lemma core_L2 (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → MeasurableSpace Ω)
    (hG : Monotone G) (b ΔB : ℕ → Ω → ℝ) (Δ C : ℝ)
    (hb_meas : ∀ k, Measurable[G k] (b k))
    (hΔB_meas : ∀ k, Measurable[G (k + 1)] (ΔB k))
    (hind : ∀ k (Z : Ω → ℝ), Measurable[G k] Z → IndepFun Z (ΔB k) P)
    (haem : ∀ k (Z : Ω → ℝ), Measurable[G k] Z → AEMeasurable Z P)
    (hbC : ∀ k ω, |b k ω| ≤ C)
    (hgauss : ∀ k, Integrable (ΔB k) P ∧ ∫ ω, ΔB k ω ∂P = 0 ∧
      Integrable (fun ω => ΔB k ω ^ 2) P ∧ ∫ ω, ΔB k ω ^ 2 ∂P = Δ) :
    ∀ m, Measurable[G m] (fun ω => ∑ k ∈ Finset.range m, b k ω * ΔB k ω) ∧
      Integrable (fun ω => (∑ k ∈ Finset.range m, b k ω * ΔB k ω) ^ 2) P ∧
      ∫ ω, (∑ k ∈ Finset.range m, b k ω * ΔB k ω) ^ 2 ∂P
        = ∑ k ∈ Finset.range m, (∫ ω, b k ω ^ 2 ∂P) * Δ := by
  have hbint : ∀ k, Integrable (fun ω => b k ω ^ 2) P := by
    intro k
    refine (integrable_const (C ^ 2)).mono' ((haem k _ (hb_meas k)).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbC k ω) 2
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hSm, hSint, hSeq⟩ := ih
    set S : Ω → ℝ := fun ω => ∑ k ∈ Finset.range m, b k ω * ΔB k ω with hS
    have hle : G m ≤ G (m + 1) := hG (Nat.le_succ m)
    have hbm : Measurable[G m] (b m) := hb_meas m
    have hmeas' : Measurable[G (m + 1)] (fun ω => ∑ k ∈ Finset.range (m + 1), b k ω * ΔB k ω) := by
      simp only [Finset.sum_range_succ]
      exact (hSm.mono hle le_rfl).add ((hbm.mono hle le_rfl).mul (hΔB_meas m))
    obtain ⟨hΔi, hΔ0, hΔ2i, hΔ2⟩ := hgauss m
    have aS : AEMeasurable S P := haem m S hSm
    have ab : AEMeasurable (b m) P := haem m _ hbm
    have aΔ : AEMeasurable (ΔB m) P := hΔi.aemeasurable
    -- cross term
    have hind1 : IndepFun (fun ω => S ω * b m ω) (ΔB m) P := hind m _ (hSm.mul hbm)
    have i1 : Integrable (fun ω => S ω ^ 2) P := hSint
    have hgdom : Integrable (fun ω => |C| * (S ω ^ 2 + ΔB m ω ^ 2)) P :=
      (i1.add hΔ2i).const_mul _
    have hcross_int : Integrable (fun ω => S ω * b m ω * ΔB m ω) P := by
      refine hgdom.mono' (aS.mul ab |>.mul aΔ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |b m ω| ≤ |C| := (hbC m ω).trans (le_abs_self C)
      have h2 : |S ω| * |ΔB m ω| ≤ S ω ^ 2 + ΔB m ω ^ 2 := by
        nlinarith [sq_nonneg (|S ω| - |ΔB m ω|), sq_abs (S ω), sq_abs (ΔB m ω)]
      calc |S ω| * |b m ω| * |ΔB m ω| = |b m ω| * (|S ω| * |ΔB m ω|) := by ring
        _ ≤ |C| * (S ω ^ 2 + ΔB m ω ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
    have hcross : ∫ ω, S ω * b m ω * ΔB m ω ∂P = 0 := by
      have := hind1.integral_mul_eq_mul_integral (aS.mul ab).aestronglyMeasurable
        aΔ.aestronglyMeasurable
      simp only [Pi.mul_apply] at this
      rw [this, hΔ0, mul_zero]
    -- diagonal term
    have hind2 : IndepFun (fun ω => b m ω ^ 2) (fun ω => ΔB m ω ^ 2) P := by
      have := (hind m (fun ω => b m ω ^ 2) (hbm.pow_const 2)).comp measurable_id
        (measurable_id.pow_const 2 : Measurable fun x : ℝ => x ^ 2)
      exact this
    have hdiag_int : Integrable (fun ω => b m ω ^ 2 * ΔB m ω ^ 2) P := by
      refine (hΔ2i.const_mul (C ^ 2)).mono' ((ab.pow_const 2).mul (aΔ.pow_const 2)).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : b m ω ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbC m ω) 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hdiag : ∫ ω, b m ω ^ 2 * ΔB m ω ^ 2 ∂P = (∫ ω, b m ω ^ 2 ∂P) * Δ := by
      have := hind2.integral_mul_eq_mul_integral (ab.pow_const 2).aestronglyMeasurable
        (aΔ.pow_const 2).aestronglyMeasurable
      simp only [Pi.mul_apply] at this
      rw [this, hΔ2]
    have hexp : (fun ω => (∑ k ∈ Finset.range (m + 1), b k ω * ΔB k ω) ^ 2) =
        fun ω => S ω ^ 2 + 2 * (S ω * b m ω * ΔB m ω) + b m ω ^ 2 * ΔB m ω ^ 2 := by
      funext ω; simp only [Finset.sum_range_succ, hS]; ring
    have i2 : Integrable (fun ω => 2 * (S ω * b m ω * ΔB m ω)) P := hcross_int.const_mul 2
    have i12 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω * b m ω * ΔB m ω)) P := i1.add i2
    have hSeq' : ∫ ω, S ω ^ 2 ∂P = ∑ k ∈ Finset.range m, (∫ ω, b k ω ^ 2 ∂P) * Δ := hSeq
    refine ⟨hmeas', ?_, ?_⟩
    · rw [hexp]
      exact i12.add hdiag_int
    · rw [hexp, integral_add i12 hdiag_int, integral_add i1 i2, integral_const_mul, hcross, hdiag,
        hSeq', Finset.sum_range_succ]
      ring

lemma trunc_sum_le (a : ℕ → ℝ) (Δ δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∀ N, ∑ k ∈ Finset.range N,
      (if ∑ j ∈ Finset.range (k + 1), a j ^ 2 * Δ < δ then a k else 0) ^ 2 * Δ ≤ max δ 0 := by
  intro N
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    by_cases h : ∑ j ∈ Finset.range (m + 1), a j ^ 2 * Δ < δ
    · rw [if_pos h]
      have hle : ∑ k ∈ Finset.range m,
          (if ∑ j ∈ Finset.range (k + 1), a j ^ 2 * Δ < δ then a k else 0) ^ 2 * Δ
          ≤ ∑ k ∈ Finset.range m, a k ^ 2 * Δ := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right _ hΔ
        split_ifs
        · exact le_rfl
        · simp; positivity
      have : ∑ j ∈ Finset.range (m + 1), a j ^ 2 * Δ =
          ∑ k ∈ Finset.range m, a k ^ 2 * Δ + a m ^ 2 * Δ := Finset.sum_range_succ _ _
      have := le_max_left δ 0
      linarith
    · rw [if_neg h]
      simpa using ih

/-- The probability estimate behind the uniqueness of the Itô integral. -/
lemma core_prob (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → MeasurableSpace Ω)
    (hG : Monotone G) (a ΔB : ℕ → Ω → ℝ) (Δ C : ℝ) (hΔ : 0 ≤ Δ)
    (ha_meas : ∀ k, Measurable[G k] (a k))
    (hΔB_meas : ∀ k, Measurable[G (k + 1)] (ΔB k))
    (hind : ∀ k (Z : Ω → ℝ), Measurable[G k] Z → IndepFun Z (ΔB k) P)
    (haem : ∀ k (Z : Ω → ℝ), Measurable[G k] Z → AEMeasurable Z P)
    (haC : ∀ k ω, |a k ω| ≤ C)
    (hgauss : ∀ k, Integrable (ΔB k) P ∧ ∫ ω, ΔB k ω ∂P = 0 ∧
      Integrable (fun ω => ΔB k ω ^ 2) P ∧ ∫ ω, ΔB k ω ^ 2 ∂P = Δ)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    P {ω | η ≤ |∑ k ∈ Finset.range N, a k ω * ΔB k ω|} ≤
      P {ω | δ ≤ ∑ k ∈ Finset.range N, a k ω ^ 2 * Δ} + ENNReal.ofReal (δ / η ^ 2) := by
  set cum : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range (k + 1), a j ω ^ 2 * Δ with hcum
  set b : ℕ → Ω → ℝ := fun k ω => if cum k ω < δ then a k ω else 0 with hb
  have hcum_meas : ∀ k, Measurable[G k] (cum k) := by
    intro k
    simp only [hcum]
    refine Finset.measurable_sum _ fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (((ha_meas j).mono (hG hj') le_rfl).pow_const 2).mul_const _
  have hb_meas : ∀ k, Measurable[G k] (b k) := by
    intro k
    simp only [hb]
    exact Measurable.ite (measurableSet_lt (hcum_meas k) measurable_const) (ha_meas k)
      measurable_const
  have hbC : ∀ k ω, |b k ω| ≤ max C 0 := by
    intro k ω
    simp only [hb]
    split_ifs
    · exact (haC k ω).trans (le_max_left _ _)
    · simp
  obtain ⟨-, hSint, hSeq⟩ := core_L2 P G hG b ΔB Δ (max C 0) hb_meas hΔB_meas hind haem hbC
    hgauss N
  -- `E[S'^2] ≤ δ`
  have hbint : ∀ k, Integrable (fun ω => b k ω ^ 2) P := by
    intro k
    refine (integrable_const ((max C 0) ^ 2)).mono'
      ((haem k _ (hb_meas k)).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbC k ω) 2
  have hE : ∫ ω, (∑ k ∈ Finset.range N, b k ω * ΔB k ω) ^ 2 ∂P ≤ δ := by
    rw [hSeq]
    have e : ∑ k ∈ Finset.range N, (∫ ω, b k ω ^ 2 ∂P) * Δ =
        ∫ ω, ∑ k ∈ Finset.range N, b k ω ^ 2 * Δ ∂P := by
      rw [integral_finset_sum _ (fun k _ => (hbint k).mul_const Δ)]
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_mul_const]
    rw [e]
    have hpt : ∀ ω, ∑ k ∈ Finset.range N, b k ω ^ 2 * Δ ≤ δ := by
      intro ω
      have := trunc_sum_le (fun j => a j ω) Δ δ hΔ N
      rw [max_eq_left hδ.le] at this
      exact this
    calc ∫ ω, ∑ k ∈ Finset.range N, b k ω ^ 2 * Δ ∂P ≤ ∫ _ω, δ ∂P :=
          integral_mono (integrable_finset_sum _ (fun k _ => (hbint k).mul_const Δ))
            (integrable_const δ) hpt
      _ = δ := by simp
  -- Chebyshev for `S'`
  set S' : Ω → ℝ := fun ω => ∑ k ∈ Finset.range N, b k ω * ΔB k ω with hS'
  have hcheb : P {ω | η ≤ |S' ω|} ≤ ENNReal.ofReal (δ / η ^ 2) := by
    have hset : {ω | η ≤ |S' ω|} = {ω | η ^ 2 ≤ S' ω ^ 2} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; nlinarith [abs_nonneg (S' ω), sq_abs (S' ω)]
      · intro h
        by_contra h'
        push Not at h'
        have : S' ω ^ 2 < η ^ 2 := by
          rw [← sq_abs]; exact pow_lt_pow_left₀ h' (abs_nonneg _) (by norm_num)
        linarith
    rw [hset]
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (ae_of_all _ fun ω => sq_nonneg (S' ω))
      hSint (η ^ 2)
    have hη2 : 0 < η ^ 2 := by positivity
    have hreal : P.real {ω | η ^ 2 ≤ S' ω ^ 2} ≤ δ / η ^ 2 := by
      rw [le_div_iff₀ hη2]; linarith
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- comparison of the events
  have hsub : {ω | η ≤ |∑ k ∈ Finset.range N, a k ω * ΔB k ω|} ⊆
      {ω | δ ≤ ∑ k ∈ Finset.range N, a k ω ^ 2 * Δ} ∪ {ω | η ≤ |S' ω|} := by
    intro ω hω
    by_cases hQ : δ ≤ ∑ k ∈ Finset.range N, a k ω ^ 2 * Δ
    · exact Or.inl hQ
    · right
      push Not at hQ
      have heq : ∑ k ∈ Finset.range N, a k ω * ΔB k ω = S' ω := by
        simp only [hS']
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k + 1 ≤ N := Finset.mem_range.mp hk
        have hc : cum k ω < δ := by
          have hmono : cum k ω ≤ ∑ k ∈ Finset.range N, a k ω ^ 2 * Δ := by
            simp only [hcum]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk')
              (fun j _ _ => by positivity)
          linarith
        simp only [hb, if_pos hc]
      simp only [Set.mem_setOf_eq] at hω ⊢
      rwa [← heq]
  calc P {ω | η ≤ |∑ k ∈ Finset.range N, a k ω * ΔB k ω|}
      ≤ P ({ω | δ ≤ ∑ k ∈ Finset.range N, a k ω ^ 2 * Δ} ∪ {ω | η ≤ |S' ω|}) := measure_mono hsub
    _ ≤ P {ω | δ ≤ ∑ k ∈ Finset.range N, a k ω ^ 2 * Δ} + P {ω | η ≤ |S' ω|} :=
        measure_union_le _ _
    _ ≤ _ := by gcongr

/-- On the `k`-th cell the elementary integrand equals `a k`. -/
lemma step_on_cell (v : ℝ≥0) (n : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) (hk : k < 2 ^ n)
    (u : ℝ) (hu : u ∈ Ioc ((k : ℝ) * v / 2 ^ n) (((k : ℝ) + 1) * v / 2 ^ n)) :
    EthierKurtz.itoStepValue v n a u ω = a k ω := by
  unfold EthierKurtz.itoStepValue
  rw [Finset.sum_eq_single k]
  · exact if_pos ⟨hu.1, hu.2⟩
  · intro j _ hjk
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hv : (0 : ℝ) ≤ v := v.2
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rcases lt_or_gt_of_ne hjk with hj | hj
    · -- `j + 1 ≤ k`
      have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      have : ((j : ℝ) + 1) * v / 2 ^ n ≤ (k : ℝ) * v / 2 ^ n := by
        apply div_le_div_of_nonneg_right _ h2n.le
        exact mul_le_mul_of_nonneg_right hj' hv
      have := hu.1
      simp only [NNReal.val_eq_coe] at h2
      linarith
    · have hj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj
      have : ((k : ℝ) + 1) * v / 2 ^ n ≤ (j : ℝ) * v / 2 ^ n := by
        apply div_le_div_of_nonneg_right _ h2n.le
        exact mul_le_mul_of_nonneg_right hj' hv
      have := hu.2
      simp only [NNReal.val_eq_coe] at h1
      linarith
  · intro hk'; exact absurd (Finset.mem_range.mpr hk) hk'

lemma step_sq_integral (v : ℝ≥0) (n : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) v)), H u.toNNReal ω = 0) :
    ∫ u in (0 : ℝ)..v, (EthierKurtz.itoStepValue v n a u ω - H u.toNNReal ω) ^ 2
      = ∑ k ∈ Finset.range (2 ^ n), a k ω ^ 2 * ((v : ℝ) / 2 ^ n) := by
  have hv : (0 : ℝ) ≤ v := v.2
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  set g : ℕ → ℝ := fun k => (k : ℝ) * v / 2 ^ n with hg
  have hgsucc : ∀ k, g (k + 1) = ((k : ℝ) + 1) * v / 2 ^ n := by intro k; simp [hg]
  have hg0 : g 0 = 0 := by simp [hg]
  have hgN : g (2 ^ n) = v := by simp only [hg]; push_cast; field_simp
  have hgle : ∀ k, g k ≤ g (k + 1) := by
    intro k; rw [hgsucc]; simp only [hg]
    apply div_le_div_of_nonneg_right _ h2n.le
    exact mul_le_mul_of_nonneg_right (by linarith) hv
  -- remove `H`
  have h1 : ∫ u in (0 : ℝ)..v, (EthierKurtz.itoStepValue v n a u ω - H u.toNNReal ω) ^ 2
      = ∫ u in (0 : ℝ)..v, (EthierKurtz.itoStepValue v n a u ω) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    rw [ae_restrict_iff' measurableSet_Ioc] at hH
    filter_upwards [hH] with u hu hmem
    rw [uIoc_of_le hv] at hmem
    rw [hu hmem, sub_zero]
  rw [h1]
  -- on each cell the integrand is constant
  have hcell : ∀ k < 2 ^ n, ∀ u ∈ Set.uIoc (g k) (g (k + 1)),
      (EthierKurtz.itoStepValue v n a u ω) ^ 2 = a k ω ^ 2 := by
    intro k hk u hu
    rw [uIoc_of_le (hgle k), hgsucc] at hu
    rw [step_on_cell v n a ω k hk u hu]
  have hint : ∀ k < 2 ^ n, IntervalIntegrable (fun u => (EthierKurtz.itoStepValue v n a u ω) ^ 2)
      volume (g k) (g (k + 1)) := by
    intro k hk
    rw [intervalIntegrable_iff]
    exact (integrableOn_const (C := a k ω ^ 2) (by simp)).congr_fun
      (fun u hu => (hcell k hk u hu).symm) measurableSet_uIoc
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hg0, hgN] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [intervalIntegral.integral_congr_ae (g := fun _ => a k ω ^ 2)
    (ae_of_all _ fun u hu => hcell k hk' u hu)]
  rw [intervalIntegral.integral_const, smul_eq_mul, hgsucc]
  simp only [hg]
  ring

/-- Uniqueness of the Itô integral of a null integrand: if `H` vanishes for a.e. time on every
path, every `J` with `HasBrownianItoIntegral` for `H` vanishes a.s. at every time. -/
theorem ito_zero (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (t₀ : ℝ) (H J : ℝ≥0 → Ω → ℝ)
    (hJ : EthierKurtz.HasBrownianItoIntegral P (shiftFiltration W t₀) (shiftBM W t₀) H J)
    (hH : ∀ ω (v : ℝ≥0), ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) v)), H u.toNNReal ω = 0)
    (v : ℝ≥0) : J v =ᵐ[P] 0 := by
  obtain ⟨a, hmeas, hbdd, hconv1, hconv2⟩ := hJ.2 v
  -- the Itô sums tend to `0` in measure
  have hS : TendstoInMeasure P (fun n => EthierKurtz.itoStepSum (shiftBM W t₀) v n (a n)) atTop
      (fun _ => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_dist] at hconv1 ⊢
    intro η hη
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    by_cases hεt : ε = ⊤
    · exact ⟨0, fun n _ => hεt ▸ le_top⟩
    set e := ε.toReal with he
    have he0 : 0 < e := ENNReal.toReal_pos hε.ne' hεt
    set δ := e * η ^ 2 / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hq := hconv1 δ hδ0
    rw [ENNReal.tendsto_atTop_zero] at hq
    obtain ⟨N, hN⟩ := hq (ENNReal.ofReal (e / 2)) (by simp; positivity)
    refine ⟨N, fun n hn => ?_⟩
    -- data for step `n`
    set gN : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * v / (2 : ℝ≥0) ^ n with hgN
    set G : ℕ → MeasurableSpace Ω := fun k => shiftFiltration W t₀ (gN k) with hG
    have hgmono : Monotone gN := by
      intro i j hij; simp only [hgN]
      gcongr
    have hGmono : Monotone G := fun i j hij => filt_mono W t₀ (hgmono hij)
    set a' : ℕ → Ω → ℝ := fun k ω => if k < 2 ^ n then a n k ω else 0 with ha'
    set ΔB : ℕ → Ω → ℝ := fun k ω => shiftBM W t₀ (gN (k + 1)) ω - shiftBM W t₀ (gN k) ω with hΔB
    obtain ⟨C, hC⟩ := hbdd n
    have ha'_meas : ∀ k, Measurable[G k] (a' k) := by
      intro k
      simp only [ha']
      split_ifs with hk
      · exact hmeas n k hk
      · exact measurable_const
    have hΔB_meas : ∀ k, Measurable[G (k + 1)] (ΔB k) := by
      intro k
      exact (shiftBM_meas W t₀ le_rfl).sub (shiftBM_meas W t₀ (hgmono (Nat.le_succ k)))
    have hind : ∀ k (Z : Ω → ℝ), Measurable[G k] Z → IndepFun Z (ΔB k) P :=
      fun k Z hZ => indep_incr P W hW t₀ (hgmono (Nat.le_succ k)) Z hZ
    have haem : ∀ k (Z : Ω → ℝ), Measurable[G k] Z → AEMeasurable Z P :=
      fun k Z hZ => aem_of_meas P W hW t₀ (gN k) Z hZ
    have haC : ∀ k ω, |a' k ω| ≤ max C 0 := by
      intro k ω; simp only [ha']
      split_ifs with hk
      · exact (hC k hk ω).trans (le_max_left _ _)
      · simp
    have hΔ : ∀ k, ((gN (k + 1) - gN k : ℝ≥0) : ℝ) = (v : ℝ) / 2 ^ n := by
      intro k
      rw [NNReal.coe_sub (hgmono (Nat.le_succ k))]
      simp only [hgN]; push_cast; ring
    have hgauss : ∀ k, Integrable (ΔB k) P ∧ ∫ ω, ΔB k ω ∂P = 0 ∧
        Integrable (fun ω => ΔB k ω ^ 2) P ∧ ∫ ω, ΔB k ω ^ 2 ∂P = (v : ℝ) / 2 ^ n := by
      intro k
      obtain ⟨-, h1, h2, h3, h4⟩ := gauss_facts (incr_law P W hW t₀ (hgmono (Nat.le_succ k)))
      exact ⟨h1, h2, h3, by rw [h4, hΔ]⟩
    have hcore := core_prob P G hGmono a' ΔB ((v : ℝ) / 2 ^ n) (max C 0) (by positivity)
      ha'_meas hΔB_meas hind haem haC hgauss (2 ^ n) hδ0 hη
    -- identify the sums
    have hSeq : ∀ ω, EthierKurtz.itoStepSum (shiftBM W t₀) v n (a n) ω =
        ∑ k ∈ Finset.range (2 ^ n), a' k ω * ΔB k ω := by
      intro ω
      unfold EthierKurtz.itoStepSum
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp only [ha', if_pos hk', hΔB, hgN]
      push_cast
      ring_nf
    have hQeq : ∀ ω, ∫ u in (0 : ℝ)..v,
        (EthierKurtz.itoStepValue v n (a n) u ω - H u.toNNReal ω) ^ 2 =
        ∑ k ∈ Finset.range (2 ^ n), a' k ω ^ 2 * ((v : ℝ) / 2 ^ n) := by
      intro ω
      rw [step_sq_integral v n (a n) ω H (hH ω v)]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [ha', if_pos (Finset.mem_range.mp hk)]
    have hN' := hN n hn
    have hset1 : {ω | η ≤ dist (EthierKurtz.itoStepSum (shiftBM W t₀) v n (a n) ω) 0} =
        {ω | η ≤ |∑ k ∈ Finset.range (2 ^ n), a' k ω * ΔB k ω|} := by
      ext ω; simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, hSeq]
    have hset2 : {ω | δ ≤ ∑ k ∈ Finset.range (2 ^ n), a' k ω ^ 2 * ((v : ℝ) / 2 ^ n)} ⊆
        {ω | δ ≤ dist (∫ u in (0 : ℝ)..v,
          (EthierKurtz.itoStepValue v n (a n) u ω - H u.toNNReal ω) ^ 2) 0} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, hQeq] at hω ⊢
      exact hω.trans (le_abs_self _)
    rw [hset1]
    calc P {ω | η ≤ |∑ k ∈ Finset.range (2 ^ n), a' k ω * ΔB k ω|}
        ≤ P {ω | δ ≤ ∑ k ∈ Finset.range (2 ^ n), a' k ω ^ 2 * ((v : ℝ) / 2 ^ n)}
          + ENNReal.ofReal (δ / η ^ 2) := hcore
      _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) := by
          have hη2 : δ / η ^ 2 = e / 2 := by rw [hδ]; field_simp
          rw [hη2]
          exact add_le_add ((measure_mono hset2).trans hN') le_rfl
      _ = ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, he,
            ENNReal.ofReal_toReal hεt]
  exact tendstoInMeasure_ae_unique hconv2 hS

end SAIto

namespace SASpike

open SmoothAmbEq.Gaussian

lemma ftc_right {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun u => ∫ s in a..u, f s) (f t) (Icc a b) t := by
  set g : ℝ → ℝ := fun s => f (max a (min s b)) with hg_def
  have hgc : Continuous g := by
    apply hf.comp_continuous (by fun_prop)
    intro s; exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hgf : EqOn g f (Icc a b) := by
    intro s hs; simp [hg_def, min_eq_left hs.2, max_eq_right hs.1]
  have hd : HasDerivAt (fun u => ∫ s in a..u, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  rw [← hgf ht]
  refine hd.hasDerivWithinAt.congr_of_mem ?_ ht
  intro u hu
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hu.1] at hs
  exact (hgf ⟨hs.1, hs.2.trans hu.2⟩).symm

/-- Uniqueness for the linear integral equation `f(s) = x₀ + ∫_{t₀}^s r f`. -/
lemma lin_unique {f : ℝ → ℝ} {t₀ T x₀ r : ℝ} (hT : t₀ ≤ T) (hf : ContinuousOn f (Icc t₀ T))
    (h : ∀ s ∈ Icc t₀ T, f s = x₀ + ∫ u in t₀..s, r * f u) :
    ∀ s ∈ Icc t₀ T, f s = x₀ * Real.exp (r * (s - t₀)) := by
  set F : ℝ → ℝ := fun s => ∫ u in t₀..s, f u with hF
  have hFd : ∀ s ∈ Icc t₀ T, HasDerivWithinAt F (f s) (Icc t₀ T) s :=
    fun s hs => ftc_right hT hf hs
  have hFeq : ∀ s ∈ Icc t₀ T, f s = x₀ + r * F s := by
    intro s hs
    rw [h s hs, hF, intervalIntegral.integral_const_mul]
  set K : ℝ → ℝ := fun s => Real.exp (-(r * (s - t₀))) * (x₀ + r * F s) with hK
  have hKd : ∀ s ∈ Icc t₀ T, HasDerivWithinAt K 0 (Icc t₀ T) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (-(r * (s - t₀))))
        (Real.exp (-(r * (s - t₀))) * (-(r * 1))) s := by
      have := ((((hasDerivAt_id' s).sub_const t₀).const_mul r).neg).exp
      simpa using this
    have := he.hasDerivWithinAt.mul (((hFd s hs).const_mul r).const_add x₀)
    refine this.congr_deriv ?_
    rw [hFeq s hs]; ring
  have hKc : ContinuousOn K (Icc t₀ T) := fun s hs => (hKd s hs).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hKc (fun x hx =>
    (hKd x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)))
  intro s hs
  have h1 := hconst s hs
  have hK0 : K t₀ = x₀ := by simp [hK, hF]
  rw [hK0] at h1
  simp only [hK] at h1
  rw [hFeq s hs]
  have hpos := Real.exp_pos (r * (s - t₀))
  have : Real.exp (-(r * (s - t₀))) * Real.exp (r * (s - t₀)) = 1 := by
    rw [← Real.exp_add]; simp
  calc x₀ + r * F s = Real.exp (r * (s - t₀)) *
        (Real.exp (-(r * (s - t₀))) * (x₀ + r * F s)) := by
          rw [← mul_assoc, mul_comm (Real.exp _) (Real.exp _), this, one_mul]
    _ = x₀ * Real.exp (r * (s - t₀)) := by rw [h1]; ring


/-- A strategy that is `c` at the single time `t₁` and `0` otherwise. -/
noncomputable def spike (t₁ c : ℝ) : Strategy := fun s _ _ => if s = t₁ then c else 0

lemma ii_of_ae_zero {f : ℝ → ℝ} {a b : ℝ} (h : ∀ᵐ u ∂volume, u ∈ Set.uIoc a b → f u = 0) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine (integrable_zero ℝ ℝ _).congr ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [h] with u hu hm
  exact (hu hm).symm

lemma ae_ne (d : ℝ) : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ d := by
  have := (Set.countable_singleton d).ae_notMem (μ := volume)
  filter_upwards [this] with u hu
  simpa using hu

variable {Ω : Type*} [MeasurableSpace Ω]

lemma wealth_zero (M : Model) (W : ℝ≥0 → Ω → ℝ) (t₁ c z t₀ β₀ : ℝ) (X : ℝ → Ω → ℝ) (ω : Ω)
    (v : ℝ≥0) : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) v)),
      wealthIntegrand M W (spike t₁ c) z t₀ β₀ X u.toNNReal ω = 0 := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_ne (t₁ - t₀)] with u hu hmem
  have hu0 : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hmem.1.le
  unfold wealthIntegrand spike
  rw [hu0]
  have : ¬ (t₀ + u = t₁) := by intro h; apply hu; linarith
  simp [this]

lemma drift_eq (M : Model) (W : ℝ≥0 → Ω → ℝ) (t₁ c z t₀ β₀ : ℝ) (X : ℝ → Ω → ℝ) (ω : Ω)
    (s : ℝ) :
    ∫ u in t₀..s, (M.r * X u ω + spike t₁ c u (X u ω) (betaZ M W z t₀ β₀ u ω) * (z - M.r))
      = ∫ u in t₀..s, M.r * X u ω := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_ne t₁] with u hu _
  simp [spike, hu]

lemma tim_zero (P : Measure Ω) [IsFiniteMeasure P] : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop
    (fun _ => (0 : ℝ)) := by
  exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => tendsto_const_nhds)

/-- The explicit solution `X_s = x₀ e^{r(s - t₀)}` for the spike strategy. -/
lemma spike_exists (M : Model) (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (t₁ c z t₀ x₀ β₀ : ℝ)
    (ht₀ : t₀ ∈ Icc 0 M.T) :
    IsInsideWealth M P W (spike t₁ c) z t₀ x₀ β₀ (fun s _ => x₀ * Real.exp (M.r * (s - t₀))) := by
  refine ⟨fun s _ => aestronglyMeasurable_const, ae_of_all _ fun ω => ?_, ae_of_all _ fun ω => ?_,
    fun _ _ => 0, ⟨?_, ?_⟩, ?_⟩
  · exact (by fun_prop : Continuous fun s : ℝ => x₀ * Real.exp (M.r * (s - t₀))).continuousOn
  · apply ii_of_ae_zero
    filter_upwards [ae_ne t₁] with u hu _
    simp [spike, hu]
  · intro t ω
    have h := wealth_zero M W t₁ c z t₀ β₀ (fun s _ => x₀ * Real.exp (M.r * (s - t₀))) ω t
    apply ii_of_ae_zero
    rw [ae_restrict_iff' measurableSet_Ioc] at h
    filter_upwards [h] with u hu hm
    rw [uIoc_of_le t.2] at hm
    rw [hu hm]; simp
  · intro t
    refine ⟨fun _ _ _ => 0, fun n k _ => measurable_const, fun n => ⟨0, fun k _ ω => by simp⟩,
      ?_, ?_⟩
    · have hz : (fun n ω => ∫ u in (0 : ℝ)..t.val,
          (EthierKurtz.itoStepValue t n ((fun _ _ _ => (0 : ℝ)) n) u ω -
            wealthIntegrand M W (spike t₁ c) z t₀ β₀
              (fun s _ => x₀ * Real.exp (M.r * (s - t₀))) u.toNNReal ω) ^ 2)
          = fun _ _ => (0 : ℝ) := by
        funext n ω
        have h := wealth_zero M W t₁ c z t₀ β₀ (fun s _ => x₀ * Real.exp (M.r * (s - t₀))) ω t
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · rw [ae_restrict_iff' measurableSet_Ioc] at h
          filter_upwards [h] with u hu hm
          rw [uIoc_of_le t.2] at hm
          rw [hu hm]
          have : EthierKurtz.itoStepValue t n ((fun _ _ _ => (0 : ℝ)) n) u ω = 0 :=
            Finset.sum_eq_zero fun k _ => by split_ifs <;> rfl
          rw [this]; norm_num
      rw [hz]
      exact tim_zero P
    · have hz : (fun n => EthierKurtz.itoStepSum (shiftBM W t₀) t n ((fun _ _ _ => (0 : ℝ)) n))
          = fun _ _ => (0 : ℝ) := by
        funext n ω; simp [EthierKurtz.itoStepSum]
      rw [hz]
      exact tim_zero P
  · intro s hs
    refine ae_of_all _ fun ω => ?_
    simp only
    rw [drift_eq M W t₁ c z t₀ β₀ (fun s _ => x₀ * Real.exp (M.r * (s - t₀))) ω s]
    have hd : ∀ u ∈ Set.uIcc t₀ s, HasDerivAt (fun u => x₀ * Real.exp (M.r * (u - t₀)))
        (M.r * (x₀ * Real.exp (M.r * (u - t₀)))) u := by
      intro u _
      have := (((hasDerivAt_id' u).sub_const t₀).const_mul M.r).exp.const_mul x₀
      refine this.congr_deriv ?_
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun u : ℝ => M.r * (x₀ * Real.exp (M.r * (u - t₀)))).intervalIntegrable _ _)]
    simp


lemma spike_unique (M : Model) (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (t₁ c z t₀ x₀ β₀ : ℝ) (ht₀ : t₀ ∈ Icc 0 M.T) (X : ℝ → Ω → ℝ)
    (hX : IsInsideWealth M P W (spike t₁ c) z t₀ x₀ β₀ X) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t₀ M.T, X s ω = x₀ * Real.exp (M.r * (s - t₀)) := by
  obtain ⟨-, hcont, -, I, hI, heq⟩ := hX
  have hI0 : ∀ v, I v =ᵐ[P] 0 := SAIto.ito_zero P W hW t₀ _ I hI
    (fun ω v => wealth_zero M W t₁ c z t₀ β₀ X ω v)
  have hT : t₀ ≤ M.T := ht₀.2
  set D : Set ℝ := insert t₀ (Ioo t₀ M.T ∩ Set.range (Rat.cast : ℚ → ℝ)) with hD
  have hDc : D.Countable :=
    ((Set.countable_range _).mono Set.inter_subset_right).insert t₀
  have hDsub : D ⊆ Icc t₀ M.T := by
    intro s hs
    rcases hs with rfl | ⟨hs, -⟩
    · exact ⟨le_rfl, hT⟩
    · exact ⟨hs.1.le, hs.2.le⟩
  have hclos : Icc t₀ M.T ⊆ closure D := by
    by_cases h : t₀ < M.T
    · have h1 : Ioo t₀ M.T ⊆ closure (Ioo t₀ M.T ∩ Set.range (Rat.cast : ℚ → ℝ)) :=
        Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
      rw [← closure_Ioo h.ne]
      calc closure (Ioo t₀ M.T) ⊆ closure (closure (Ioo t₀ M.T ∩ Set.range (Rat.cast : ℚ → ℝ))) :=
            closure_mono h1
        _ = closure (Ioo t₀ M.T ∩ Set.range (Rat.cast : ℚ → ℝ)) := closure_closure
        _ ⊆ closure D := closure_mono (Set.subset_insert _ _)
    · intro s hs
      have : s = t₀ := le_antisymm (by linarith [hs.2, not_lt.mp h]) hs.1
      rw [this]
      exact subset_closure (Set.mem_insert _ _)
  have hae : ∀ᵐ ω ∂P, ∀ s ∈ D, X s ω = x₀ + ∫ u in t₀..s, M.r * X u ω := by
    rw [ae_ball_iff hDc]
    intro s hs
    filter_upwards [heq s (hDsub hs), hI0 (s - t₀).toNNReal] with ω h1 h2
    rw [h1, drift_eq M W t₁ c z t₀ β₀ X ω s, h2]
    simp
  filter_upwards [hae, hcont] with ω h1 h2
  have hrX : ContinuousOn (fun u => M.r * X u ω) (Icc t₀ M.T) := h2.const_smul M.r
  have hF : ContinuousOn (fun s => x₀ + ∫ u in t₀..s, M.r * X u ω) (Icc t₀ M.T) :=
    fun s hs => ((ftc_right hT hrX hs).const_add x₀).continuousWithinAt
  have hEq : EqOn (fun s => X s ω) (fun s => x₀ + ∫ u in t₀..s, M.r * X u ω) (Icc t₀ M.T) :=
    Set.EqOn.of_subset_closure (fun s hs => h1 s hs) h2 hF hDsub hclos
  exact lin_unique hT h2 hEq

/-- The spike strategy is admissible. -/
lemma spike_admissible (M : Model) (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (t₁ c : ℝ) : Admissible M P W (spike t₁ c) := by
  have hk := M.hk
  refine ⟨fun z t₀ ht₀ x₀ β₀ => ⟨⟨_, spike_exists M P W t₁ c z t₀ x₀ β₀ ht₀⟩, ?_⟩, ?_⟩
  · intro X Y hX hY
    filter_upwards [spike_unique M P W hW t₁ c z t₀ x₀ β₀ ht₀ X hX,
      spike_unique M P W hW t₁ c z t₀ x₀ β₀ ht₀ Y hY] with ω h1 h2 s hs
    rw [h1 s hs, h2 s hs]
  · intro t₀ ht₀ x₀ β₀ ε hε ρ hρ
    set K1 := Real.exp (-3 * M.k * Real.exp (M.r * (M.T - t₀)) * x₀) with hK1
    set C := K1 + |c| ^ ρ + 1 with hC
    have hC0 : 0 < C := by positivity
    refine ⟨3, by norm_num, (t₀ + M.T) / 2, ⟨by linarith [ht₀.2], by linarith [ht₀.2]⟩, C, hC0,
      fun z X hX s hs => ?_⟩
    have hs' : s ∈ Icc t₀ M.T := ⟨hs.1, hs.2.trans (by linarith [ht₀.2])⟩
    have hez : 1 ≤ Real.exp (ε * z ^ 2) := Real.one_le_exp (by positivity)
    have hCle : C ≤ C * Real.exp (ε * z ^ 2) := le_mul_of_one_le_right hC0.le hez
    constructor
    · have hu := spike_unique M P W hW t₁ c z t₀ x₀ β₀ ⟨ht₀.1, ht₀.2.le⟩ X hX
      calc (∫⁻ ω, ENNReal.ofReal (Real.exp (-3 * M.k * Real.exp (M.r * (M.T - s)) * X s ω)) ∂P)
          = ∫⁻ _ω, ENNReal.ofReal K1 ∂P := by
            apply lintegral_congr_ae
            filter_upwards [hu] with ω hω
            rw [hω s hs', hK1]
            congr 2
            have : Real.exp (M.r * (M.T - s)) * Real.exp (M.r * (s - t₀))
                = Real.exp (M.r * (M.T - t₀)) := by rw [← Real.exp_add]; ring_nf
            calc -3 * M.k * Real.exp (M.r * (M.T - s)) * (x₀ * Real.exp (M.r * (s - t₀)))
                = -3 * M.k * (Real.exp (M.r * (M.T - s)) * Real.exp (M.r * (s - t₀))) * x₀ := by
                  ring
              _ = _ := by rw [this]
        _ = ENNReal.ofReal K1 := by simp
        _ ≤ ENNReal.ofReal (C * Real.exp (ε * z ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            have : K1 ≤ C := by
              rw [hC]; have : 0 ≤ |c| ^ ρ := by positivity
              linarith
            linarith
    · have hpt : ∀ ω, |spike t₁ c s (X s ω) (betaZ M W z t₀ β₀ s ω)| ^ ρ ≤ |c| ^ ρ := by
        intro ω
        unfold spike
        split_ifs
        · exact le_rfl
        · rw [abs_zero, Real.zero_rpow (by linarith)]; positivity
      calc (∫⁻ ω, ENNReal.ofReal (|spike t₁ c s (X s ω) (betaZ M W z t₀ β₀ s ω)| ^ ρ) ∂P)
          ≤ ∫⁻ _ω, ENNReal.ofReal (|c| ^ ρ) ∂P :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
        _ = ENNReal.ofReal (|c| ^ ρ) := by simp
        _ ≤ ENNReal.ofReal (C * Real.exp (ε * z ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            have : |c| ^ ρ ≤ C := by rw [hC]; have := Real.exp_pos (-3 * M.k * Real.exp (M.r * (M.T - t₀)) * x₀); linarith
            linarith

end SASpike

open SmoothAmbEq.Gaussian

theorem solution (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) :
    ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
      (∀ π : Strategy, Admissible M P W π →
        Integrable (fun z => M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β)
          (posterior M t β)) ∧
      IsLUB {v : ℝ | ∃ π : Strategy, Admissible M P W π ∧
        v = ∫ z, M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β
          ∂(posterior M t β)} 0 := by
  intro t ht x β
  refine ⟨fun π _ => (SAL53.value_formula M c hc t ht x β (π t x β)).1, ?_, ?_⟩
  · rintro v ⟨π, -, rfl⟩
    obtain ⟨K₀, hK₀, heq⟩ := (SAL53.value_formula M c hc t ht x β (π t x β)).2
    rw [heq]
    have := mul_nonneg hK₀ (sq_nonneg (π t x β - piStar M c t x β))
    linarith
  · intro b hb
    apply hb
    refine ⟨SASpike.spike t (piStar M c t x β), SASpike.spike_admissible M P W hW _ _, ?_⟩
    obtain ⟨K₀, -, heq⟩ :=
      (SAL53.value_formula M c hc t ht x β (SASpike.spike t (piStar M c t x β) t x β)).2
    have hsp : SASpike.spike t (piStar M c t x β) t x β = piStar M c t x β := by
      simp [SASpike.spike]
    rw [heq, hsp]
    simp
