-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:59:06.794285+00:00
-- url     : https://prove2.me/submissions/ec19b541-3f35-4bea-9356-3ef1e33f074e

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_lemma_5_3_eq_5_13

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SAE53

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

end SAE53

open SmoothAmbEq.Gaussian SAE53

theorem solution (M : Model) (c : Coeffs) (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    (∀ t ∈ Icc 0 M.T,
      c.m₄ t = -M.r * c.m₁ t - M.r * c.m₂ t ∧ c.m₅ t = -M.r * c.m₂ t - M.r * c.m₃ t) ∧
    (∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
      (∀ π : Strategy, Admissible M P W π →
        Integrable (fun z => M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β)
          (posterior M t β)) ∧
      IsLUB {v : ℝ | ∃ π : Strategy, Admissible M P W π ∧
        v = ∫ z, M.φ' (gz M c z t x β) * gen M z (π t x β) (gz M c z) t x β
          ∂(posterior M t β)} 0) ∧
    (∀ z : ℝ, ∀ t ∈ Icc 0 M.T, ∀ x β : ℝ,
      gen M z (piStar M c t x β) (gz M c z) t x β = 0) ∧
    (∀ z x β : ℝ, gz M c z M.T x β = -(1 / M.k) * Real.exp (-M.k * x)) := by
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
  refine ⟨fun t ht => ⟨hm4 t ht, hm5 t ht⟩,
    lemma_5_3_eq_5_13 M c hc P W hW, ?_, ?_⟩
  · -- (5.14)
    intro z t ht x β
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
  · -- (5.15)
    intro z x β
    simp [gz, fz, h1T, h2T, h3T, h4T, h5T, h6T]
