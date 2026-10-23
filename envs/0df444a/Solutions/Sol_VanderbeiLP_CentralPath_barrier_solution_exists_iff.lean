-- Prove2me | solution 1 for VanderbeiLP.CentralPath.barrier_solution_exists_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:36:14.350584+00:00
-- url     : https://prove2.me/submissions/1d00be3f-ab22-4f7b-a8f0-7d8cf17d87a9

import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

set_option autoImplicit false

open Matrix Filter Topology

namespace VanderbeiCPAux

open VanderbeiLP.CentralPath

lemma phi_bound (μ a s : ℝ) (hμ : 0 < μ) (ha : 0 < a) (hs : 0 < s) :
    μ * Real.log s - a * s ≤ (μ * Real.log (2 * μ / a) - μ) - a * s / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < s * (a / (2 * μ)) by positivity)
  rw [Real.log_mul hs.ne' (by positivity), Real.log_div (by positivity) (by positivity)] at h1
  rw [Real.log_div (by positivity) ha.ne']
  have h2 := mul_le_mul_of_nonneg_left h1 hμ.le
  have h3 : μ * (s * (a / (2 * μ)) - 1) = a * s / 2 - μ := by
    field_simp
  rw [h3] at h2
  nlinarith

lemma coord_bounds (μ a s D : ℝ) (hμ : 0 < μ) (ha : 0 < a) (hs : 0 < s)
    (h : (μ * Real.log (2 * μ / a) - μ) - (μ * Real.log s - a * s) ≤ D) :
    Real.exp (((μ * Real.log (2 * μ / a) - μ) - D) / μ) ≤ s ∧ s ≤ 2 * D / a := by
  have hb := phi_bound μ a s hμ ha hs
  constructor
  · have hlog : ((μ * Real.log (2 * μ / a) - μ) - D) / μ ≤ Real.log s := by
      rw [div_le_iff₀ hμ]
      nlinarith [mul_pos ha hs]
    calc Real.exp (((μ * Real.log (2 * μ / a) - μ) - D) / μ) ≤ Real.exp (Real.log s) :=
          Real.exp_le_exp.mpr hlog
      _ = s := Real.exp_log hs
  · rw [le_div_iff₀ ha]
    nlinarith

lemma rewrite_f {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (y0 : Fin m → ℝ) (z0 : Fin n → ℝ) (hc0 : Aᵀ *ᵥ y0 - z0 = c)
    (x : Fin n → ℝ) (w : Fin m → ℝ) (hb : A *ᵥ x + w = b) :
    barrierFunction c μ x w = y0 ⬝ᵥ b + (∑ j, (μ * Real.log (x j) - z0 j * x j))
      + ∑ i, (μ * Real.log (w i) - y0 i * w i) := by
  have hcx : c ⬝ᵥ x = y0 ⬝ᵥ b - y0 ⬝ᵥ w - z0 ⬝ᵥ x := by
    rw [← hc0, ← hb, sub_dotProduct, dotProduct_add, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec]
    ring
  unfold barrierFunction
  rw [hcx]
  simp only [dotProduct, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- First-order condition at a barrier maximizer, coordinate `j`. -/
lemma first_order {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) (h : IsBarrierSolution A b c μ x w) (j : Fin n) :
    c j + μ * (1 / x j) + μ * ∑ i, (-A i j) / w i = 0 := by
  obtain ⟨hAx, hx, hw, hmax⟩ := h
  set e : Fin n → ℝ := Pi.single j 1 with he
  let g : ℝ → ℝ := fun t => (c ⬝ᵥ x + t * c j) + μ * ∑ k, Real.log (x k + t * e k)
      + μ * ∑ i, Real.log (w i + t * (-A i j))
  have hd : HasDerivAt g (c j + μ * ∑ k, e k / (x k + 0 * e k)
      + μ * ∑ i, (-A i j) / (w i + 0 * (-A i j))) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => c ⬝ᵥ x + t * c j) (c j) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (c j)).const_add (c ⬝ᵥ x)
    have h2 : HasDerivAt (fun t : ℝ => ∑ k, Real.log (x k + t * e k))
        (∑ k, e k / (x k + 0 * e k)) 0 := by
      apply HasDerivAt.fun_sum
      intro k _
      have hk : HasDerivAt (fun t : ℝ => x k + t * e k) (e k) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (e k)).const_add (x k)
      exact hk.log (by simpa using (hx k).ne')
    have h3 : HasDerivAt (fun t : ℝ => ∑ i, Real.log (w i + t * (-A i j)))
        (∑ i, (-A i j) / (w i + 0 * (-A i j))) 0 := by
      apply HasDerivAt.fun_sum
      intro i _
      have hi : HasDerivAt (fun t : ℝ => w i + t * (-A i j)) (-A i j) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (-A i j)).const_add (w i)
      exact hi.log (by simpa using (hw i).ne')
    exact (h1.add (h2.const_mul μ)).add (h3.const_mul μ)
  have hloc : IsLocalMax g 0 := by
    have ex : ∀ k, ∀ᶠ t in 𝓝 (0:ℝ), 0 < x k + t * e k := by
      intro k
      have ht : Tendsto (fun t : ℝ => x k + t * e k) (𝓝 0) (𝓝 (x k + 0 * e k)) :=
        ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
      exact ht.eventually (lt_mem_nhds (by simpa using hx k))
    have ew : ∀ i, ∀ᶠ t in 𝓝 (0:ℝ), 0 < w i + t * (-A i j) := by
      intro i
      have ht : Tendsto (fun t : ℝ => w i + t * (-A i j)) (𝓝 0) (𝓝 (w i + 0 * (-A i j))) :=
        ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
      exact ht.eventually (lt_mem_nhds (by simpa using hw i))
    filter_upwards [Filter.eventually_all.2 ex, Filter.eventually_all.2 ew] with t htx htw
    have hc : A *ᵥ (fun k => x k + t * e k) + (fun i => w i + t * (-A i j)) = b := by
      rw [← hAx]
      funext i
      have : (fun k => x k + t * e k) = x + t • e := by
        funext k; simp [smul_eq_mul]
      rw [this, Matrix.mulVec_add, Matrix.mulVec_smul, he, Matrix.mulVec_single_one]
      simp [Matrix.col_apply]
      ring
    have := hmax (fun k => x k + t * e k) (fun i => w i + t * (-A i j)) hc htx htw
    have hg0 : g 0 = barrierFunction c μ x w := by
      simp [g, barrierFunction]
    have hgt : g t = barrierFunction c μ (fun k => x k + t * e k) (fun i => w i + t * (-A i j)) := by
      simp only [g, barrierFunction]
      congr 2
      simp [he, dotProduct, Pi.single_apply, mul_add, Finset.sum_add_distrib]
      try ring
    rw [hg0, hgt]
    exact this
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hs : ∑ k, e k / (x k + 0 * e k) = 1 / x j := by
    simp [he, Pi.single_apply, ite_div]
  rw [hs] at h0
  simpa using h0

lemma forward {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (hμ : 0 < μ) (x : Fin n → ℝ) (w : Fin m → ℝ) (h : IsBarrierSolution A b c μ x w) :
    PrimalStrictlyFeasible A b ∧ DualStrictlyFeasible A c := by
  refine ⟨⟨x, w, h.1, h.2.1, h.2.2.1⟩, ⟨fun i => μ / w i, fun j => μ / x j, ?_,
    fun i => div_pos hμ (h.2.2.1 i), fun j => div_pos hμ (h.2.1 j)⟩⟩
  funext j
  have hf := first_order A b c μ x w h j
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have : ∑ i, A i j * (μ / w i) = - (μ * ∑ i, (-A i j) / w i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this]
  have : μ / x j = μ * (1 / x j) := by ring
  rw [this]
  linarith

lemma backward {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (hμ : 0 < μ) (hP : PrimalStrictlyFeasible A b) (hD : DualStrictlyFeasible A c) :
    ∃ (x : Fin n → ℝ) (w : Fin m → ℝ), IsBarrierSolution A b c μ x w := by
  obtain ⟨x0, w0, hb0, hx0, hw0⟩ := hP
  obtain ⟨y0, z0, hc0, hy0, hz0⟩ := hD
  set U : ℝ → ℝ := fun a => μ * Real.log (2 * μ / a) - μ with hU
  set T : ℝ := ∑ j, U (z0 j) + ∑ i, U (y0 i) with hT
  set C : ℝ := barrierFunction c μ x0 w0 - y0 ⬝ᵥ b with hC
  set D : ℝ := T - C with hD
  set lx : Fin n → ℝ := fun j => Real.exp ((U (z0 j) - D) / μ) with hlx
  set ux : Fin n → ℝ := fun j => 2 * D / z0 j with hux
  set lw : Fin m → ℝ := fun i => Real.exp ((U (y0 i) - D) / μ) with hlw
  set uw : Fin m → ℝ := fun i => 2 * D / y0 i with huw
  set K : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
    {p | A *ᵥ p.1 + p.2 = b} ∩ Set.Icc (lx, lw) (ux, uw) with hK
  -- key bound: superlevel points lie in the box
  have hbox : ∀ (x : Fin n → ℝ) (w : Fin m → ℝ), A *ᵥ x + w = b → (∀ j, 0 < x j) →
      (∀ i, 0 < w i) → barrierFunction c μ x0 w0 ≤ barrierFunction c μ x w → (x, w) ∈ K := by
    intro x w hb hx hw hle
    have hr := rewrite_f A b c μ y0 z0 hc0 x w hb
    have hnx : ∀ j, 0 ≤ U (z0 j) - (μ * Real.log (x j) - z0 j * x j) := by
      intro j
      have := phi_bound μ (z0 j) (x j) hμ (hz0 j) (hx j)
      have := mul_pos (hz0 j) (hx j)
      simp only [hU]; linarith
    have hnw : ∀ i, 0 ≤ U (y0 i) - (μ * Real.log (w i) - y0 i * w i) := by
      intro i
      have := phi_bound μ (y0 i) (w i) hμ (hy0 i) (hw i)
      have := mul_pos (hy0 i) (hw i)
      simp only [hU]; linarith
    have hsum : (∑ j, (U (z0 j) - (μ * Real.log (x j) - z0 j * x j)))
        + ∑ i, (U (y0 i) - (μ * Real.log (w i) - y0 i * w i)) ≤ D := by
      have heq : (∑ j, (U (z0 j) - (μ * Real.log (x j) - z0 j * x j)))
          + ∑ i, (U (y0 i) - (μ * Real.log (w i) - y0 i * w i))
          = T - (barrierFunction c μ x w - y0 ⬝ᵥ b) := by
        rw [hr, hT]
        simp only [Finset.sum_sub_distrib]
        ring
      rw [heq, hD, hC]
      linarith
    have hSx : 0 ≤ ∑ j, (U (z0 j) - (μ * Real.log (x j) - z0 j * x j)) :=
      Finset.sum_nonneg (fun j _ => hnx j)
    have hSw : 0 ≤ ∑ i, (U (y0 i) - (μ * Real.log (w i) - y0 i * w i)) :=
      Finset.sum_nonneg (fun i _ => hnw i)
    have bx : ∀ j, lx j ≤ x j ∧ x j ≤ ux j := by
      intro j
      have h1 : U (z0 j) - (μ * Real.log (x j) - z0 j * x j) ≤ D := by
        have := Finset.single_le_sum (f := fun j => U (z0 j) - (μ * Real.log (x j) - z0 j * x j))
          (fun j _ => hnx j) (Finset.mem_univ j)
        linarith
      exact coord_bounds μ (z0 j) (x j) D hμ (hz0 j) (hx j) h1
    have bw : ∀ i, lw i ≤ w i ∧ w i ≤ uw i := by
      intro i
      have h1 : U (y0 i) - (μ * Real.log (w i) - y0 i * w i) ≤ D := by
        have := Finset.single_le_sum (f := fun i => U (y0 i) - (μ * Real.log (w i) - y0 i * w i))
          (fun i _ => hnw i) (Finset.mem_univ i)
        linarith
      exact coord_bounds μ (y0 i) (w i) D hμ (hy0 i) (hw i) h1
    refine ⟨hb, ⟨⟨fun j => (bx j).1, fun i => (bw i).1⟩, ⟨fun j => (bx j).2, fun i => (bw i).2⟩⟩⟩
  have hlxpos : ∀ j, 0 < lx j := fun j => Real.exp_pos _
  have hlwpos : ∀ i, 0 < lw i := fun i => Real.exp_pos _
  have hKpos : ∀ p ∈ K, (∀ j, 0 < p.1 j) ∧ ∀ i, 0 < p.2 i := by
    intro p hp
    exact ⟨fun j => lt_of_lt_of_le (hlxpos j) (hp.2.1.1 j),
      fun i => lt_of_lt_of_le (hlwpos i) (hp.2.1.2 i)⟩
  have hKc : IsCompact K := by
    apply IsCompact.inter_left isCompact_Icc
    apply isClosed_eq
    · exact ((Matrix.mulVecLin A).continuous_of_finiteDimensional.comp continuous_fst).add
        continuous_snd
    · exact continuous_const
  have hK0 : (x0, w0) ∈ K := hbox x0 w0 hb0 hx0 hw0 le_rfl
  have hcont : ContinuousOn (fun p : (Fin n → ℝ) × (Fin m → ℝ) => barrierFunction c μ p.1 p.2) K := by
    unfold barrierFunction
    apply ContinuousOn.add
    apply ContinuousOn.add
    · apply Continuous.continuousOn
      simp only [dotProduct]
      exact continuous_finsetSum _ (fun j _ => continuous_const.mul
        ((continuous_apply j).comp continuous_fst))
    · apply ContinuousOn.mul continuousOn_const
      apply continuousOn_finsetSum
      intro j _
      apply ContinuousOn.log
      · exact ((continuous_apply j).comp continuous_fst).continuousOn
      · intro p hp; exact ((hKpos p hp).1 j).ne'
    · apply ContinuousOn.mul continuousOn_const
      apply continuousOn_finsetSum
      intro i _
      apply ContinuousOn.log
      · exact ((continuous_apply i).comp continuous_snd).continuousOn
      · intro p hp; exact ((hKpos p hp).2 i).ne'
  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨_, hK0⟩ hcont
  refine ⟨p.1, p.2, hpK.1, (hKpos p hpK).1, (hKpos p hpK).2, ?_⟩
  intro x' w' hb' hx' hw'
  have hp0 : barrierFunction c μ x0 w0 ≤ barrierFunction c μ p.1 p.2 := hpmax hK0
  by_cases hle : barrierFunction c μ x0 w0 ≤ barrierFunction c μ x' w'
  · exact hpmax (hbox x' w' hb' hx' hw' hle)
  · linarith [not_le.mp hle]

end VanderbeiCPAux

open VanderbeiLP.CentralPath in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (hμ : 0 < μ) :
    (∃ (x : Fin n → ℝ) (w : Fin m → ℝ), IsBarrierSolution A b c μ x w) ↔
      PrimalStrictlyFeasible A b ∧ DualStrictlyFeasible A c := by
  constructor
  · rintro ⟨x, w, h⟩
    exact VanderbeiCPAux.forward A b c μ hμ x w h
  · rintro ⟨hP, hD⟩
    exact VanderbeiCPAux.backward A b c μ hμ hP hD
