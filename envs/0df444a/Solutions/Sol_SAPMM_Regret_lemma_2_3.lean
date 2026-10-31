-- Prove2me | solution 1 for SAPMM.Regret.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:20:27.694863+00:00
-- url     : https://prove2.me/submissions/eabb1ff6-efa5-4d22-b4c6-141a8034855e

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxA

open SAPMM.Regret

lemma projPos_apply {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    projPos y i = max (y i) 0 := rfl

lemma norm_sq_sum {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq y

lemma norm_le_of_sum {p : ℕ} {a b : EuclideanSpace ℝ (Fin p)}
    (h : ∑ i, (a i) ^ 2 ≤ ∑ i, (b i) ^ 2) : ‖a‖ ≤ ‖b‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_sum, norm_sq_sum]
  exact h

lemma norm_projPos_le {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : ‖projPos y‖ ≤ ‖y‖ := by
  apply norm_le_of_sum
  apply Finset.sum_le_sum
  intro i _
  rw [projPos_apply]
  rcases le_total (y i) 0 with h | h
  · rw [max_eq_right h]; simpa using sq_nonneg (y i)
  · rw [max_eq_left h]

lemma projPos_lip {p : ℕ} (a b : EuclideanSpace ℝ (Fin p)) :
    ‖projPos a - projPos b‖ ≤ ‖a - b‖ := by
  apply norm_le_of_sum
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, projPos_apply]
  have := abs_max_sub_max_le_abs (a i) (b i) 0
  rw [← sq_abs (max (a i) 0 - max (b i) 0), ← sq_abs (a i - b i)]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma projPos_of_nonneg {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (h : ∀ i, 0 ≤ y i) :
    projPos y = y := by
  ext i
  rw [projPos_apply, max_eq_left (h i)]

section run

variable {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Problem n p Ξ} {σ α : ℝ} {x0 : EuclideanSpace ℝ (Fin n)} {ξ : ℕ → Ω → Ξ}
  {x : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {lam : ℕ → Ω → EuclideanSpace ℝ (Fin p)}

lemma lam_nonneg (hrun : IsRun P σ α x0 ξ x lam) : ∀ t ω i, 0 ≤ lam t ω i := by
  intro t ω i
  cases t with
  | zero => rw [hrun.lam_zero]; simp
  | succ t => rw [hrun.lam_succ, projPos_apply]; exact le_max_right _ _

lemma x_mem (hrun : IsRun P σ α x0 ξ x lam) (hx0 : x0 ∈ P.X0) : ∀ t ω, x t ω ∈ P.X0 := by
  intro t ω
  cases t with
  | zero => rw [hrun.x_zero]; exact hx0
  | succ t => exact hrun.x_mem t ω

end run


section conv

lemma convex_maxsq {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ s f) (c σ : ℝ) (hσ : 0 ≤ σ) :
    ConvexOn ℝ s (fun y => (max (c + σ * f y) 0) ^ 2) := by
  have h1 : ConvexOn ℝ s (fun y => max (c + σ * f y) 0) := by
    refine ⟨hf.1, fun a ha b hb u v hu hv huv => ?_⟩
    have hfab := hf.2 ha hb hu hv huv
    simp only [smul_eq_mul] at hfab ⊢
    apply max_le
    · have e1 : c + σ * (u * f a + v * f b) = u * (c + σ * f a) + v * (c + σ * f b) := by
        linear_combination (-c) * huv
      calc c + σ * f (u • a + v • b) ≤ c + σ * (u * f a + v * f b) := by
            have := mul_le_mul_of_nonneg_left hfab hσ; linarith
        _ = u * (c + σ * f a) + v * (c + σ * f b) := e1
        _ ≤ u * max (c + σ * f a) 0 + v * max (c + σ * f b) 0 := by
            have := mul_le_mul_of_nonneg_left (le_max_left (c + σ * f a) 0) hu
            have := mul_le_mul_of_nonneg_left (le_max_left (c + σ * f b) 0) hv
            linarith
    · have := mul_nonneg hu (le_max_right (c + σ * f a) 0)
      have := mul_nonneg hv (le_max_right (c + σ * f b) 0)
      linarith
  exact h1.pow (fun y _ => le_max_right _ _) 2

lemma convex_finsum {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))} (hs : Convex ℝ s) {ι : Type*}
    (I : Finset ι) (f : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun y => ∑ i ∈ I, f i y) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) hs
  | insert a I ha ih =>
    have := (hf a).add ih
    refine this.congr ?_
    intro y _
    simp [Finset.sum_insert ha]

lemma norm_comb_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) (u : ℝ) :
    ‖(1 - u) • a + u • b‖ ^ 2 = (1 - u) * ‖a‖ ^ 2 + u * ‖b‖ ^ 2 - u * (1 - u) * ‖a - b‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

lemma three_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : Set E}
    {φ : E → ℝ} (hφ : ConvexOn ℝ s φ) (c z : E) (hz : z ∈ s) {α : ℝ} (hα : 0 < α)
    (hmin : ∀ y ∈ s, φ z + α / 2 * ‖z - c‖ ^ 2 ≤ φ y + α / 2 * ‖y - c‖ ^ 2) :
    ∀ y ∈ s, φ z + α / 2 * ‖z - c‖ ^ 2 + α / 2 * ‖y - z‖ ^ 2 ≤ φ y + α / 2 * ‖y - c‖ ^ 2 := by
  intro y hy
  have key : ∀ u : ℝ, 0 < u → u ≤ 1 / 2 →
      φ z + α / 2 * ‖z - c‖ ^ 2 + α / 2 * ‖y - z‖ ^ 2 ≤
        φ y + α / 2 * ‖y - c‖ ^ 2 + u * (α / 2 * ‖y - z‖ ^ 2) := by
    intro u hu hu2
    have hw : (1 - u) • z + u • y ∈ s := hφ.1 hz hy (by linarith) hu.le (by ring)
    have h1 := hmin _ hw
    have h2 := hφ.2 hz hy (by linarith : (0:ℝ) ≤ 1 - u) hu.le (by ring)
    simp only [smul_eq_mul] at h2
    have h3 : (1 - u) • z + u • y - c = (1 - u) • (z - c) + u • (y - c) := by
      module
    rw [h3, norm_comb_sq] at h1
    have h4 : z - c - (y - c) = -(y - z) := by abel
    rw [h4, norm_neg] at h1
    have hd : 0 ≤ ‖y - z‖ ^ 2 := sq_nonneg _
    have h5 : u * (φ z + α / 2 * ‖z - c‖ ^ 2 + α / 2 * ‖y - z‖ ^ 2) ≤
        u * (φ y + α / 2 * ‖y - c‖ ^ 2 + u * (α / 2 * ‖y - z‖ ^ 2)) := by
      nlinarith
    exact le_of_mul_le_mul_left h5 hu
  apply le_of_forall_pos_le_add
  intro ε hε
  set K := α / 2 * ‖y - z‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set u := min (1 / 2) (ε / (K + 1)) with hu
  have hu0 : 0 < u := lt_min (by norm_num) (div_pos hε (by linarith))
  have hu2 : u ≤ 1 / 2 := min_le_left _ _
  have hu3 : u * K ≤ ε := by
    have : u ≤ ε / (K + 1) := min_le_right _ _
    have h' : u * (K + 1) ≤ ε := by
      rw [le_div_iff₀ (by linarith)] at this; exact this
    nlinarith
  have := key u hu0 hu2
  linarith

end conv

end SAPMM.Regret.AuxA

open SAPMM.Regret SAPMM.Regret.AuxA

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : SAPMM.Regret.Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : SAPMM.Regret.IsRun P σ α x0 ξ x lam) :
    ∀ t ω, ∀ y ∈ P.X0,
      P.F (x (t + 1) ω) (ξ t ω) + 1 / (2 * σ) * ‖lam (t + 1) ω‖ ^ 2
          + α / 2 * ‖x (t + 1) ω - x t ω‖ ^ 2 ≤
        P.F y (ξ t ω) + 1 / (2 * σ) * ‖SAPMM.Regret.projPos (lam t ω + σ • P.G y (ξ t ω))‖ ^ 2
          + α / 2 * (‖y - x t ω‖ ^ 2 - ‖y - x (t + 1) ω‖ ^ 2) := by
  intro t ω y hy
  set L := lam t ω
  set ξv := ξ t ω
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => P.F y ξv + 1 / (2 * σ) * ‖SAPMM.Regret.projPos (L + σ • P.G y ξv)‖ ^ 2 with hψ
  have hconvS : ConvexOn ℝ P.X0
      (fun y => ‖SAPMM.Regret.projPos (L + σ • P.G y ξv)‖ ^ 2) := by
    have := convex_finsum hP.X0_convex Finset.univ
      (fun i y => (max (L i + σ * P.G y ξv i) 0) ^ 2)
      (fun i => convex_maxsq ((hP.G_conv ξv i).subset hP.X0_sub_O0 hP.X0_convex) (L i) σ hσ.le)
    refine this.congr ?_
    intro y _
    simp only
    rw [norm_sq_sum]
    simp [projPos_apply]
  have hconv : ConvexOn ℝ P.X0 ψ := by
    have hF := (hP.F_conv ξv).subset hP.X0_sub_O0 hP.X0_convex
    have := hF.add (hconvS.smul (c := 1 / (2 * σ)) (by positivity))
    refine this.congr ?_
    intro y _
    simp [hψ, smul_eq_mul]
  have hmin : ∀ y ∈ P.X0, ψ (x (t + 1) ω) + α / 2 * ‖x (t + 1) ω - x t ω‖ ^ 2 ≤
      ψ y + α / 2 * ‖y - x t ω‖ ^ 2 := by
    intro y hy
    have := (isMinOn_iff.1 (hrun.x_min t ω)) y hy
    simp only [SAPMM.Regret.augLag] at this
    simp only [hψ]
    linarith
  have := three_point hconv (x t ω) (x (t + 1) ω) (hrun.x_mem t ω) hα hmin y hy
  simp only [hψ] at this
  rw [hrun.lam_succ t ω]
  linarith
