-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.stepGarding_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:18.816491+00:00
-- url     : https://prove2.me/submissions/2c8d0b9e-331a-4b15-ab3b-c4e4efea8181

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
import Theorems.Thm_PI_KFinSmoothW_Gard_contDiff_mat_mul
import Theorems.Thm_PI_KFinSmoothW_Gard_contDiff_mat_conjT
import Theorems.Thm_PI_KFinSmoothW_Gard_umat_measEmb
import Theorems.Thm_PI_KFinSmoothW_Gard_tau_gv
import Theorems.Thm_PI_KFinSmoothW_Gard_Lsm_apply
import Theorems.Thm_PI_KFinSmoothW_Gard_locInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
section Calc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}
end Calc
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
private theorem matrix_norm_mul_le_card_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ‖A * B‖ ≤ m * ‖A‖ * ‖B‖ := by
  have h0 : 0 ≤ (m : ℝ) * ‖A‖ * ‖B‖ := by positivity
  rw [Matrix.norm_le_iff h0]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, ‖A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = m * ‖A‖ * ‖B‖ := by simp [mul_assoc]
end Gard
end PI.KFinSmoothW
end
end

set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
namespace PI.KFinSmoothW.Gard
theorem _root_.solution : StepGarding := by
  intro n ε H _ _ _ τ hτ Φ hΦ hΦc x
  unfold SmoothJ SmoothOnH
  intro g₀ hg₀
  have hl : (Jm ε * g₀ᴴ * Jm ε) * g₀ = 1 := coeMatrix_left_inv ε g₀ hg₀
  have hr : g₀ * (Jm ε * g₀ᴴ * Jm ε) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hl
  set A : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun p => Jm ε * pᴴ * Jm ε with hA
  have hAc : ContDiff ℝ ∞ A :=
    contDiff_mat_mul (contDiff_mat_mul contDiff_const (contDiff_mat_conjT contDiff_id)) contDiff_const

  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport Φ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity,
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  set c : ℝ := (n : ℝ) * ‖g₀‖ with hc
  have hc0 : 0 ≤ c := by positivity
  set U : Set (Matrix (Fin n) (Fin n) ℂ) := {p | (n : ℝ) * c * ‖A p - A g₀‖ < 1 / 2} with hU
  have hUo : IsOpen U :=
    isOpen_lt (continuous_const.mul ((hAc.continuous.sub continuous_const).norm)) continuous_const
  have hg₀U : g₀ ∈ U := by
    show (n : ℝ) * c * ‖A g₀ - A g₀‖ < 1 / 2
    simp

  have hk : ∀ p ∈ U, ∀ y, Φ (A p * (-y)) ≠ 0 → ‖y‖ ≤ 2 * c * R := by
    intro p hp y hy
    have hp' : (n : ℝ) * c * ‖A p - A g₀‖ < 1 / 2 := hp
    have hz : ‖A p * (-y)‖ ≤ R := by
      have h0 := hR (subset_tsupport _ hy)
      simpa using h0
    have h1 : -y = g₀ * (A g₀ * (-y)) := by
      rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
    have h2 : A g₀ * (-y) = A p * (-y) - (A p - A g₀) * (-y) := by
      rw [Matrix.sub_mul]
      abel
    have e1 := matrix_norm_mul_le_card_mul g₀ (A g₀ * (-y))
    have e2 := matrix_norm_mul_le_card_mul (A p - A g₀) (-y)
    rw [← h1, norm_neg] at e1
    rw [norm_neg] at e2
    have e3 : ‖A g₀ * (-y)‖ ≤ ‖A p * (-y)‖ + ‖(A p - A g₀) * (-y)‖ := by
      rw [h2]
      exact norm_sub_le _ _
    have e4 : ‖A g₀ * (-y)‖ ≤ R + n * ‖A p - A g₀‖ * ‖y‖ := by linarith
    have e5 : ‖y‖ ≤ c * (R + n * ‖A p - A g₀‖ * ‖y‖) := by
      calc ‖y‖ ≤ n * ‖g₀‖ * ‖A g₀ * (-y)‖ := e1
        _ ≤ c * (R + n * ‖A p - A g₀‖ * ‖y‖) := by
          rw [hc]
          exact mul_le_mul_of_nonneg_left e4 (by positivity)
    have e6 : c * (n * ‖A p - A g₀‖ * ‖y‖) ≤ 1 / 2 * ‖y‖ := by
      have h3 := mul_le_mul_of_nonneg_right hp'.le (norm_nonneg y)
      linarith
    linarith
  have hgs : ∀ (p y : Matrix (Fin n) (Fin n) ℂ), p ∈ U → y ∉ Metric.closedBall 0 (2 * c * R) →
      Φ (A p * (-y)) = 0 := by
    intro p y hp hy
    by_contra h
    exact hy (mem_closedBall_zero_iff.mpr (hk p hp y h))
  have hGs : ContDiff ℝ ∞ (fun q : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      Φ (A q.1 * (-q.2))) :=
    hΦ.comp (contDiff_mat_mul (hAc.comp contDiff_fst) contDiff_snd.neg)
  have hconv := MeasureTheory.contDiffOn_convolution_right_with_param (𝕜 := ℝ)
    (μ := Measure.map umat (muG ε)) (f := fun t => τ t x) (n := ⊤) (Lsm H)
    (g := fun p y => Φ (A p * (-y))) hUo (isCompact_closedBall 0 (2 * c * R)) hgs (locInt hτ x)
    hGs.contDiffOn
  refine ⟨U, fun p => MeasureTheory.convolution (fun t => τ t x) (fun y => Φ (A p * (-y))) (Lsm H)
    (Measure.map umat (muG ε)) 0, hUo, hg₀U, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ => (p, (0 : Matrix (Fin n) (Fin n) ℂ))) U :=
      contDiffOn_id.prodMk contDiffOn_const
    have h4 : Set.MapsTo (fun p : Matrix (Fin n) (Fin n) ℂ => (p, (0 : Matrix (Fin n) (Fin n) ℂ))) U
        (U ×ˢ Set.univ) := fun p hp => ⟨hp, Set.mem_univ _⟩
    have h5 := ContDiffOn.comp hconv h2 h4
    exact h5
  · intro g _ hg
    have hgl : (Jm ε * gᴴ * Jm ε) * g = 1 := coeMatrix_left_inv ε g hg
    have hgr : g * (Jm ε * gᴴ * Jm ε) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hgl
    let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, hgr, hgl⟩
    let γ : UJ ε := ⟨u, hg⟩
    have hγ : umat γ = g := rfl
    beta_reduce
    rw [← hγ, tau_gv hτ Φ hΦ.continuous hΦc x γ, hγ, MeasureTheory.convolution_def,
      (umat_measEmb ε).integral_map]
    congr 1
    funext h
    rw [Lsm_apply, zero_sub, neg_neg]
end PI.KFinSmoothW.Gard
