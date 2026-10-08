-- Prove2me | solution 1 for SuttonTD.Convergence.powers_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:10:31.168461+00:00
-- url     : https://prove2.me/submissions/4256d410-c743-45d1-b013-903afb0deb11

import Mathlib
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal

set_option autoImplicit false

open Filter Topology Matrix

namespace P9fa16a21

lemma quad_homog {N : Type*} [Fintype N] (S : Matrix N N ℝ) (t : ℝ) (v : N → ℝ) :
    (t • v) ⬝ᵥ (S *ᵥ (t • v)) = t ^ 2 * (v ⬝ᵥ (S *ᵥ v)) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma quad_cont {N : Type*} [Fintype N] (S : Matrix N N ℝ) :
    Continuous (fun v : N → ℝ => v ⬝ᵥ (S *ᵥ v)) := by
  simp only [dotProduct, mulVec]
  fun_prop

lemma quad_scale {N : Type*} [Fintype N] (S : Matrix N N ℝ) (v : N → ℝ) (hv : v ≠ 0) :
    v ⬝ᵥ (S *ᵥ v) = ‖v‖ ^ 2 * ((‖v‖⁻¹ • v) ⬝ᵥ (S *ᵥ (‖v‖⁻¹ • v))) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [quad_homog]
  field_simp

lemma sphere_mem {N : Type*} [Fintype N] (v : N → ℝ) (hv : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ Metric.sphere (0 : N → ℝ) 1 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp [norm_smul, hn]

lemma quad_lower {N : Type*} [Fintype N] (S : Matrix N N ℝ)
    (hS : ∀ v : N → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (S *ᵥ v)) :
    ∃ c > 0, ∀ v : N → ℝ, c * ‖v‖ ^ 2 ≤ v ⬝ᵥ (S *ᵥ v) := by
  by_cases h : ∃ v : N → ℝ, v ≠ 0
  · obtain ⟨w, hw⟩ := h
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : N → ℝ) 1).exists_isMinOn
      ⟨_, sphere_mem w hw⟩ (quad_cont S).continuousOn
    have hu0 : u ≠ 0 := by
      intro h0; simp [h0] at hu
    refine ⟨u ⬝ᵥ (S *ᵥ u), hS u hu0, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp
    · have h1 := isMinOn_iff.mp hmin _ (sphere_mem v hv)
      rw [quad_scale S v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · push Not at h
    refine ⟨1, one_pos, fun v => ?_⟩
    rw [h v]; simp

lemma quad_upper {N : Type*} [Fintype N] (S : Matrix N N ℝ) :
    ∃ C > 0, ∀ v : N → ℝ, v ⬝ᵥ (S *ᵥ v) ≤ C * ‖v‖ ^ 2 := by
  by_cases h : ∃ v : N → ℝ, v ≠ 0
  · obtain ⟨w, hw⟩ := h
    obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : N → ℝ) 1).exists_isMaxOn
      ⟨_, sphere_mem w hw⟩ (quad_cont S).continuousOn
    refine ⟨max (u ⬝ᵥ (S *ᵥ u)) 1, by positivity, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp
    · have h1 := isMaxOn_iff.mp hmax _ (sphere_mem v hv)
      rw [quad_scale S v hv, mul_comm (max _ _)]
      exact mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (by positivity)
  · push Not at h
    refine ⟨1, one_pos, fun v => ?_⟩
    rw [h v]; simp

end P9fa16a21

open Filter Topology Matrix SuttonTD.Convergence in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}
    (X : Matrix (Fin K) N ℝ) (hX : LinearIndependent ℝ (fun i : N => fun k : Fin K => X k i))
    (M : Matrix N N ℝ) (hM : IsPosDefReal M) :
    ∃ ε > 0, ∀ α : ℝ, 0 < α → α < ε →
      Tendsto (fun n : ℕ => (1 - α • (Xᵀ * X * M)) ^ n) atTop (𝓝 0) := by
  classical
  set G : Matrix N N ℝ := Xᵀ * X with hGdef
  have hXinj : ∀ v : N → ℝ, X *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hsum : ∑ i, v i • (fun k : Fin K => X k i) = 0 := by
      rw [← hv]; ext k; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    funext i
    exact Fintype.linearIndependent_iff.mp hX v hsum i
  have hGq : ∀ v, v ⬝ᵥ (G *ᵥ v) = (X *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
    intro v
    rw [hGdef, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hself : ∀ w : Fin K → ℝ, w ≠ 0 → 0 < w ⬝ᵥ w := by
    intro w hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (w j))
      ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
  have hGpos : ∀ v : N → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (G *ᵥ v) := by
    intro v hv
    rw [hGq]
    exact hself _ (fun h => hv (hXinj v h))
  have hGT : Gᵀ = G := by simp [hGdef, transpose_mul]
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hGv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h0
    have := hGpos v hv
    rw [hGv, dotProduct_zero] at this
    exact lt_irrefl _ this
  set P : Matrix N N ℝ := G⁻¹ with hPdef
  have hPG : P * G = 1 := nonsing_inv_mul G hdet
  have hGP : G * P = 1 := mul_nonsing_inv G hdet
  have hPT : Pᵀ = P := by rw [hPdef, transpose_nonsing_inv, hGT]
  have hPpos : ∀ v : N → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (P *ᵥ v) := by
    intro v hv
    have hw : G *ᵥ (P *ᵥ v) = v := by rw [mulVec_mulVec, hGP, one_mulVec]
    have hw0 : P *ᵥ v ≠ 0 := by
      intro h; apply hv; rw [← hw, h, mulVec_zero]
    have := hGpos _ hw0
    rw [hw] at this
    rwa [dotProduct_comm]
  set A : Matrix N N ℝ := G * M with hAdef
  have hPA : P * A = M := by rw [hAdef, ← Matrix.mul_assoc, hPG, Matrix.one_mul]
  have cross1 : ∀ v, v ⬝ᵥ (P *ᵥ (A *ᵥ v)) = v ⬝ᵥ (M *ᵥ v) := by
    intro v; rw [mulVec_mulVec, hPA]
  have cross2 : ∀ v, (A *ᵥ v) ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    intro v
    rw [dotProduct_comm, ← vecMul_transpose P v, ← dotProduct_mulVec, hPT, cross1]
  have hAq : ∀ v, (A *ᵥ v) ⬝ᵥ (P *ᵥ (A *ᵥ v)) = v ⬝ᵥ ((Aᵀ * P * A) *ᵥ v) := by
    intro v
    rw [show (Aᵀ * P * A) *ᵥ v = Aᵀ *ᵥ (P *ᵥ (A *ᵥ v)) by rw [mulVec_mulVec, mulVec_mulVec],
      dotProduct_mulVec v Aᵀ, vecMul_transpose]
  obtain ⟨c1, hc1, hm⟩ := P9fa16a21.quad_lower M hM
  obtain ⟨c3, hc3, hql⟩ := P9fa16a21.quad_lower P hPpos
  obtain ⟨C2, hC2, hqu⟩ := P9fa16a21.quad_upper P
  obtain ⟨C4, hC4, hAu⟩ := P9fa16a21.quad_upper (Aᵀ * P * A)
  have hq0 : ∀ v : N → ℝ, 0 ≤ v ⬝ᵥ (P *ᵥ v) := fun v => le_trans (by positivity) (hql v)
  have hmq : ∀ v : N → ℝ, (c1 / C2) * (v ⬝ᵥ (P *ᵥ v)) ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    calc (c1 / C2) * (v ⬝ᵥ (P *ᵥ v)) ≤ (c1 / C2) * (C2 * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hqu v) (by positivity)
      _ = c1 * ‖v‖ ^ 2 := by field_simp
      _ ≤ _ := hm v
  have hAqb : ∀ v : N → ℝ,
      (A *ᵥ v) ⬝ᵥ (P *ᵥ (A *ᵥ v)) ≤ (C4 / c3) * (v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    calc (A *ᵥ v) ⬝ᵥ (P *ᵥ (A *ᵥ v)) = v ⬝ᵥ ((Aᵀ * P * A) *ᵥ v) := hAq v
      _ ≤ C4 * ‖v‖ ^ 2 := hAu v
      _ = (C4 / c3) * (c3 * ‖v‖ ^ 2) := by field_simp
      _ ≤ (C4 / c3) * (v ⬝ᵥ (P *ᵥ v)) := mul_le_mul_of_nonneg_left (hql v) (by positivity)
  set c := c1 / C2 with hcdef
  set D := C4 / c3 with hDdef
  have hc : 0 < c := by positivity
  have hD : 0 < D := by positivity
  refine ⟨min (c / D) (1 / c), by positivity, ?_⟩
  intro α hα hαε
  have hα1 : α < c / D := lt_of_lt_of_le hαε (min_le_left _ _)
  have hα2 : α < 1 / c := lt_of_lt_of_le hαε (min_le_right _ _)
  have hαD : α * D < c := (lt_div_iff₀ hD).mp hα1
  have hαc : α * c < 1 := (lt_div_iff₀ hc).mp hα2
  set B : Matrix N N ℝ := 1 - α • A with hBdef
  have hBv : ∀ v, B *ᵥ v = v - α • (A *ᵥ v) := by
    intro v; simp [hBdef, sub_mulVec, Matrix.smul_mulVec]
  set r := 1 - α * c with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; nlinarith
  have hstep : ∀ v, (B *ᵥ v) ⬝ᵥ (P *ᵥ (B *ᵥ v)) ≤ r * (v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    rw [hBv]
    have hexp : (v - α • (A *ᵥ v)) ⬝ᵥ (P *ᵥ (v - α • (A *ᵥ v)))
        = v ⬝ᵥ (P *ᵥ v) - α * (v ⬝ᵥ (P *ᵥ (A *ᵥ v))) - α * ((A *ᵥ v) ⬝ᵥ (P *ᵥ v))
          + α ^ 2 * ((A *ᵥ v) ⬝ᵥ (P *ᵥ (A *ᵥ v))) := by
      simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [hexp, cross1, cross2]
    have h0 := hq0 v
    have h1 : α * (c * (v ⬝ᵥ (P *ᵥ v))) ≤ α * (v ⬝ᵥ (M *ᵥ v)) :=
      mul_le_mul_of_nonneg_left (hmq v) hα.le
    have h2 : α ^ 2 * ((A *ᵥ v) ⬝ᵥ (P *ᵥ (A *ᵥ v))) ≤ α ^ 2 * (D * (v ⬝ᵥ (P *ᵥ v))) :=
      mul_le_mul_of_nonneg_left (hAqb v) (sq_nonneg _)
    have h3 : (α * (v ⬝ᵥ (P *ᵥ v))) * (α * D) ≤ (α * (v ⬝ᵥ (P *ᵥ v))) * c :=
      mul_le_mul_of_nonneg_left hαD.le (mul_nonneg hα.le h0)
    rw [hrdef]
    nlinarith
  have hpow : ∀ (n : ℕ) (v : N → ℝ),
      ((B ^ n) *ᵥ v) ⬝ᵥ (P *ᵥ ((B ^ n) *ᵥ v)) ≤ r ^ n * (v ⬝ᵥ (P *ᵥ v)) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', ← mulVec_mulVec]
      calc _ ≤ r * (((B ^ n) *ᵥ v) ⬝ᵥ (P *ᵥ ((B ^ n) *ᵥ v))) := hstep _
        _ ≤ r * (r ^ n * (v ⬝ᵥ (P *ᵥ v))) := mul_le_mul_of_nonneg_left (ih v) hr0.le
        _ = r ^ (n + 1) * (v ⬝ᵥ (P *ᵥ v)) := by ring
  have hvec : ∀ v : N → ℝ, Tendsto (fun n : ℕ => (B ^ n) *ᵥ v) atTop (𝓝 0) := by
    intro v
    have hnorm : ∀ n : ℕ, ‖(B ^ n) *ᵥ v‖ ≤ Real.sqrt (r ^ n * (v ⬝ᵥ (P *ᵥ v)) / c3) := by
      intro n
      have hsq : ‖(B ^ n) *ᵥ v‖ ^ 2 ≤ r ^ n * (v ⬝ᵥ (P *ᵥ v)) / c3 := by
        rw [le_div_iff₀ hc3, mul_comm]
        exact (hql _).trans (hpow n v)
      have := Real.abs_le_sqrt hsq
      rwa [abs_of_nonneg (norm_nonneg _)] at this
    have hlim : Tendsto (fun n : ℕ => Real.sqrt (r ^ n * (v ⬝ᵥ (P *ᵥ v)) / c3)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => r ^ n * (v ⬝ᵥ (P *ᵥ v)) / c3) atTop
          (𝓝 (0 * (v ⬝ᵥ (P *ᵥ v)) / c3)) :=
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).mul_const _).div_const _
      rw [zero_mul, zero_div] at h1
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      exact h2
    exact squeeze_zero_norm hnorm hlim
  have key : ∀ i j, Tendsto (fun n : ℕ => (B ^ n) i j) atTop (𝓝 0) := by
    intro i j
    have h := tendsto_pi_nhds.mp (hvec (Pi.single j 1)) i
    simp only [Pi.zero_apply] at h
    refine h.congr (fun n => ?_)
    simp [mulVec, dotProduct, Pi.single_apply]
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => key i j
