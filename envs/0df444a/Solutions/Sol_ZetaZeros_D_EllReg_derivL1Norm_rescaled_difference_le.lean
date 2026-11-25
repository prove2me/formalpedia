-- Prove2me | solution 1 for ZetaZeros.D.EllReg.derivL1Norm_rescaled_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:05.982312+00:00
-- url     : https://prove2.me/submissions/0c9e9991-fbe7-4038-a897-77e8d88eb97a

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernGr
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
import Theorems.Thm_ZetaZeros_D_EllReg_gr_pos
import Theorems.Thm_ZetaZeros_D_EllReg_gr_zero
import Theorems.Thm_ZetaZeros_D_EllReg_integrable_iteratedFDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
set_option maxHeartbeats 800000
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (ψ : E d → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (x0 : E d) (r0 : ℝ) (n : ℕ) :
    ∃ K : ℝ, ∀ r : ℝ, 0 < r → r ≤ r0 →
      derivL1Norm (fun y => ψ y * (b (x0 + r • y) - b x0)) n ≤ K * r := by
  classical
  have hinf : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun m => by exact_mod_cast le_top
  have hbnd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := (hb.continuous_iteratedFDeriv (hinf k)).norm.bddAbove_range_of_hasCompactSupport
      (hbc.iteratedFDeriv (𝕜 := ℝ) k).norm
    exact ⟨max M 0, le_max_right _ _, fun x => (hM ⟨x, rfl⟩).trans (le_max_left _ _)⟩
  choose M hM0 hM using hbnd
  obtain ⟨L0, hL0⟩ := (hb.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hbc.fderiv (𝕜 := ℝ)).norm
  have hL : ∀ x, ‖fderiv ℝ b x‖ ≤ max L0 0 := fun x => (hL0 ⟨x, rfl⟩).trans (le_max_left _ _)
  have hLn : 0 ≤ max L0 0 := le_max_right _ _
  have hR1 : 1 ≤ max 1 r0 := le_max_left _ _
  have hsumn : 0 ≤ ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hM0 k) (by positivity)
  have hAL : max L0 0 ≤ max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k :=
    le_add_of_nonneg_right hsumn
  have hAk : ∀ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k ≤
      max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k := fun k hk =>
    (Finset.single_le_sum (f := fun k => M k * (max 1 r0) ^ k)
      (fun k _ => mul_nonneg (hM0 k) (by positivity)) hk).trans (le_add_of_nonneg_left hLn)
  have hA0 : 0 ≤ max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k := hLn.trans hAL
  set A := max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k with hA
  let h : ℕ → E d → ℝ := fun j y =>
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)
  have hhi : ∀ j, Integrable (h j) := by
    intro j
    show Integrable (fun y =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖))
    refine integrable_finset_sum _ fun i _ => ?_
    have h0 := integrable_iteratedFDeriv hψ hψc 0 i
    have h1 := integrable_iteratedFDeriv hψ hψc 1 i
    have he : (fun y => (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)) = fun y =>
        (j.choose i : ℝ) * (‖y‖ ^ 0 * ‖iteratedFDeriv ℝ i ψ y‖ + ‖y‖ ^ 1 * ‖iteratedFDeriv ℝ i ψ y‖) := by
      funext y
      ring
    rw [he]
    exact (h0.add h1).const_mul _
  refine ⟨A * ∑ j ∈ Finset.range (n + 1), ∫ y, h j y, fun r hr hr0 => ?_⟩
  have hg : ContDiff ℝ ∞ (fun y => b (x0 + r • y) - b x0) := by
    have h1 : ContDiff ℝ ∞ (fun y : E d => x0 + r • y) := by fun_prop
    exact (hb.comp h1).sub contDiff_const
  have hgb : ∀ k ∈ Finset.range (n + 1), ∀ y,
      ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ r * A * (1 + ‖y‖) := by
    intro k hk y
    have hy : 0 ≤ ‖y‖ := norm_nonneg _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [norm_iteratedFDeriv_zero]
      have h1 := gr_zero b hb (max L0 0) hL x0 y r hr
      nlinarith [mul_le_mul_of_nonneg_left hAL (mul_nonneg hr.le hy), mul_nonneg hr.le hA0]
    · have h1 := gr_pos b hb k hk0 (M k) (hM k) x0 y r hr
      have hrk : r ^ k ≤ r * (max 1 r0) ^ k := by
        calc r ^ k = r * r ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk0]
          _ ≤ r * (max 1 r0) ^ (k - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (hr0.trans (le_max_right _ _)) _) hr.le
          _ ≤ r * (max 1 r0) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (Nat.sub_le _ _)) hr.le
      have h2 : M k * r ^ k ≤ r * A := by
        calc M k * r ^ k ≤ M k * (r * (max 1 r0) ^ k) := mul_le_mul_of_nonneg_left hrk (hM0 k)
          _ = r * (M k * (max 1 r0) ^ k) := by ring
          _ ≤ r * A := mul_le_mul_of_nonneg_left (hAk k hk) hr.le
      nlinarith [mul_nonneg (mul_nonneg hr.le hA0) hy]
  have hpt : ∀ j ∈ Finset.range (n + 1), ∀ y,
      ‖iteratedFDeriv ℝ j (fun y => ψ y * (b (x0 + r • y) - b x0)) y‖ ≤ r * A * h j y := by
    intro j hj y
    refine (norm_iteratedFDeriv_mul_le hψ hg y (hinf j)).trans ?_
    simp only [h, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hji : j - i ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
    have h3 := hgb (j - i) hji y
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ := by positivity
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => b (x0 + r • y) - b x0) y‖
        ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (r * A * (1 + ‖y‖)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = r * A * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)) := by ring
  unfold derivL1Norm
  calc ∑ j ∈ Finset.range (n + 1), ∫ y, ‖iteratedFDeriv ℝ j (fun y => ψ y * (b (x0 + r • y) - b x0)) y‖
      ≤ ∑ j ∈ Finset.range (n + 1), ∫ y, r * A * h j y := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          ((hhi j).const_mul _) (Filter.Eventually.of_forall fun y => hpt j hj y)
    _ = (A * ∑ j ∈ Finset.range (n + 1), ∫ y, h j y) * r := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        ring
end ZetaZeros.D.EllReg
