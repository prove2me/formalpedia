-- Prove2me | solution 1 for SuttonTD.Convergence.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:18:51.124161+00:00
-- url     : https://prove2.me/submissions/37e0185c-1e87-4b1e-ae8b-2a8807627622
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SuttonTD_Convergence_ExpectedVisits
import Definitions.Def_SuttonTD_Convergence_EpisodeStream
import Definitions.Def_SuttonTD_Convergence_LinearTD0
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
import Theorems.Thm_SuttonTD_Convergence_expected_update
import Theorems.Thm_SuttonTD_Convergence_expected_visits_eq
import Theorems.Thm_SuttonTD_Convergence_key_matrix_posDef
import Theorems.Thm_SuttonTD_Convergence_powers_tendsto_zero

set_option autoImplicit false

open Filter Topology MeasureTheory Matrix

namespace SuttonTD123020ea

/-- Child E: the closing step of Sutton's proof of Theorem 2. -/
theorem affine_recursion_tendsto {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}
    (X : Matrix (Fin K) N ℝ) (d : N → ℝ) (Q : Matrix N N ℝ) (h : N → ℝ) (α : ℝ)
    (hQ : IsUnit (1 - Q))
    (hB : Tendsto (fun n : ℕ => (1 - α • (Xᵀ * X * (diagonal d * (1 - Q)))) ^ n) atTop (𝓝 0))
    (w : ℕ → Fin K → ℝ)
    (hw : ∀ n, w (n + 1) = w n + α • ((X * diagonal d) *ᵥ (h + Q *ᵥ (Xᵀ *ᵥ w n) - Xᵀ *ᵥ w n)))
    (i : N) :
    Tendsto (fun n => (Xᵀ *ᵥ w n) i) atTop (𝓝 (((1 - Q)⁻¹ *ᵥ h) i)) := by
  set B : Matrix N N ℝ := 1 - α • (Xᵀ * X * (diagonal d * (1 - Q))) with hBdef
  set ps : N → ℝ := (1 - Q)⁻¹ *ᵥ h with hps
  have hh : h = (1 - Q) *ᵥ ps := by
    rw [hps, mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ),
      one_mulVec]
  have hstep : ∀ n, Xᵀ *ᵥ w (n + 1) - ps = B *ᵥ (Xᵀ *ᵥ w n - ps) := by
    intro n
    have e1 : h + Q *ᵥ (Xᵀ *ᵥ w n) - Xᵀ *ᵥ w n = (1 - Q) *ᵥ (ps - Xᵀ *ᵥ w n) := by
      rw [hh, mulVec_sub, sub_mulVec, sub_mulVec, one_mulVec, one_mulVec]; abel
    rw [hw n, e1, mulVec_add, mulVec_smul, mulVec_mulVec, mulVec_mulVec, hBdef, sub_mulVec,
      one_mulVec, smul_mulVec, mulVec_sub (Xᵀ * X * (diagonal d * (1 - Q)))]
    have : Xᵀ * (X * diagonal d) * (1 - Q) = Xᵀ * X * (diagonal d * (1 - Q)) := by
      simp only [Matrix.mul_assoc]
    rw [this]
    simp only [mulVec_sub, smul_sub]
    abel
  have hpow : ∀ n, Xᵀ *ᵥ w n - ps = B ^ n *ᵥ (Xᵀ *ᵥ w 0 - ps) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hstep n, ih, mulVec_mulVec, pow_succ']
  have hlim : Tendsto (fun n => B ^ n *ᵥ (Xᵀ *ᵥ w 0 - ps)) atTop (𝓝 0) := by
    have hc : Continuous (fun A : Matrix N N ℝ => A *ᵥ (Xᵀ *ᵥ w 0 - ps)) :=
      continuous_id.matrix_mulVec continuous_const
    have := (hc.tendsto 0).comp hB
    simpa [Function.comp_def] using this
  have hlim2 : Tendsto (fun n => Xᵀ *ᵥ w n) atTop (𝓝 ps) := by
    have := hlim.add_const ps
    simp only [zero_add] at this
    refine this.congr (fun n => ?_)
    rw [← hpow n]; abel
  exact (continuous_apply i).continuousAt.tendsto.comp hlim2

end SuttonTD123020ea

universe uN uT uΩ

open SuttonTD.Convergence in
/-- Glue: Theorem 2 from the four milestones A (expected_update), B (expected_visits_eq),
C (key_matrix_posDef), D (powers_tendsto_zero), plus child E above. -/
theorem theorem_2_of_children {N : Type uN} {T : Type uT} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (μ : N → ℝ)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    {K : ℕ} (x : N → Fin K → ℝ) (hx : LinearIndependent ℝ x)
    (hd : ∀ i, 0 < C.expectedVisits μ i)
    (hB : ∀ i, HasSum (fun p : List N × T => C.pathWeight μ p.1 p.2 * (p.1.count i : ℝ))
      ((μ ᵥ* (1 - C.Q)⁻¹) i))
    (hC : (∀ i, 0 < (μ ᵥ* (1 - C.Q)⁻¹) i) →
      IsPosDefReal (diagonal (μ ᵥ* (1 - C.Q)⁻¹) * (1 - C.Q)))
    (hD : ∀ (X : Matrix (Fin K) N ℝ), LinearIndependent ℝ (fun i : N => fun k : Fin K => X k i) →
      ∀ (M : Matrix N N ℝ), IsPosDefReal M →
      ∃ ε > 0, ∀ α : ℝ, 0 < α → α < ε →
        Tendsto (fun n : ℕ => (1 - α • (Xᵀ * X * M)) ^ n) atTop (𝓝 0))
    (hA : ∀ (α : ℝ) (w₀ : Fin K → ℝ) (Ω : Type uΩ) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (e : ℕ → Ω → Episode N T), IsEpisodeStream C μ ν P e → ∀ n : ℕ,
      (∀ k, Integrable (fun ω => tdWeights x α w₀ e n ω k) P) ∧
        (fun k => ∫ ω, tdWeights x α w₀ e (n + 1) ω k ∂P) =
          (fun k => ∫ ω, tdWeights x α w₀ e n ω k ∂P) +
            α • (((Matrix.of fun k i => x i k) * diagonal (C.expectedVisits μ)) *ᵥ
              (C.h (fun j => ∫ z, z ∂ν j) +
                C.Q *ᵥ ((Matrix.of fun k i => x i k)ᵀ *ᵥ (fun k => ∫ ω, tdWeights x α w₀ e n ω k ∂P)) -
                (Matrix.of fun k i => x i k)ᵀ *ᵥ (fun k => ∫ ω, tdWeights x α w₀ e n ω k ∂P)))) :
    ∃ ε > 0, ∀ α : ℝ, 0 < α → α < ε → ∀ (w₀ : Fin K → ℝ)
      {Ω : Type uΩ} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (e : ℕ → Ω → Episode N T), IsEpisodeStream C μ ν P e →
      ∀ i : N, (∀ n, Integrable (fun ω => x i ⬝ᵥ tdWeights x α w₀ e n ω) P) ∧
        Tendsto (fun n => ∫ ω, x i ⬝ᵥ tdWeights x α w₀ e n ω ∂P) atTop
          (𝓝 (((1 - C.Q)⁻¹ *ᵥ C.h (fun j => ∫ z, z ∂ν j)) i)) := by
  classical
  have hdfun : C.expectedVisits μ = μ ᵥ* (1 - C.Q)⁻¹ := funext fun i => (hB i).tsum_eq
  have hd' : ∀ i, 0 < (μ ᵥ* (1 - C.Q)⁻¹) i := fun i => hdfun ▸ hd i
  have hpd := hC hd'
  set X : Matrix (Fin K) N ℝ := Matrix.of fun k i => x i k with hXdef
  have hX : LinearIndependent ℝ (fun i : N => fun k : Fin K => X k i) := by
    simpa [hXdef] using hx
  obtain ⟨ε, hε, hconv⟩ := hD X hX _ hpd
  refine ⟨ε, hε, fun α hα hαε w₀ Ω _ P _ e he i => ?_⟩
  have hUn : IsUnit (1 - C.Q) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    by_contra hnu
    have h0 : (1 - C.Q)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hnu
    obtain ⟨i0⟩ : Nonempty N := ⟨i⟩
    have := hd' i0
    rw [h0] at this
    simp at this
  set wbar : ℕ → Fin K → ℝ := fun m k => ∫ ω, tdWeights x α w₀ e m ω k ∂P with hwbar
  have hdot : ∀ n ω, x i ⬝ᵥ tdWeights x α w₀ e n ω = ∑ k, x i k * tdWeights x α w₀ e n ω k :=
    fun n ω => rfl
  have hint : ∀ n, Integrable (fun ω => x i ⬝ᵥ tdWeights x α w₀ e n ω) P := by
    intro n
    simp only [hdot]
    exact integrable_finsetSum _ fun k _ => ((hA α w₀ Ω P e he n).1 k).const_mul _
  refine ⟨hint, ?_⟩
  have hval : ∀ n, ∫ ω, x i ⬝ᵥ tdWeights x α w₀ e n ω ∂P = (Xᵀ *ᵥ wbar n) i := by
    intro n
    simp only [hdot]
    rw [integral_finsetSum _ fun k _ => ((hA α w₀ Ω P e he n).1 k).const_mul _]
    simp only [integral_const_mul, mulVec, dotProduct, hXdef, transpose_apply, of_apply, hwbar]
  simp only [hval]
  refine SuttonTD123020ea.affine_recursion_tendsto X (μ ᵥ* (1 - C.Q)⁻¹) C.Q _ α hUn
    (hconv α hα hαε) wbar (fun n => ?_) i
  have := (hA α w₀ Ω P e he n).2
  rw [hdfun] at this
  exact this

open SuttonTD.Convergence in
theorem solution {N T : Type*} [Fintype N] [DecidableEq N] [Nonempty N] [Fintype T] [Nonempty T]
    (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (ν : T → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (hν : ∀ j, Integrable id (ν j))
    {K : ℕ} (x : N → Fin K → ℝ) (hx : LinearIndependent ℝ x)
    (hd : ∀ i, 0 < C.expectedVisits μ i) :
    ∃ ε > 0, ∀ α : ℝ, 0 < α → α < ε → ∀ (w₀ : Fin K → ℝ)
      {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (e : ℕ → Ω → Episode N T), IsEpisodeStream C μ ν P e →
      ∀ i : N, (∀ n, Integrable (fun ω => x i ⬝ᵥ tdWeights x α w₀ e n ω) P) ∧
        Tendsto (fun n => ∫ ω, x i ⬝ᵥ tdWeights x α w₀ e n ω ∂P) atTop
          (𝓝 (((1 - C.Q)⁻¹ *ᵥ C.h (fun j => ∫ z, z ∂ν j)) i)) :=
  theorem_2_of_children C μ ν x hx hd
    (fun i => SuttonTD.Convergence.expected_visits_eq C μ hμ0 hμ1 i)
    (fun h => SuttonTD.Convergence.key_matrix_posDef C μ hμ0 hμ1 h)
    (fun X hX M hM => SuttonTD.Convergence.powers_tendsto_zero X hX M hM)
    (fun α w₀ _ _ P _ e he n => SuttonTD.Convergence.expected_update C μ hμ0 hμ1 ν hν x α w₀ P e he n)
