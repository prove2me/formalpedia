-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lintegral_pi_complex_monomial_e34694584652
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:43.085132+00:00
-- url     : https://prove2.me/submissions/9d2a42b3-e168-46b2-bb45-996f2cc374a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FubiniStudyIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_complex_norm_pow_div_c13acad093c9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set Filter Topology Real
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k : ℕ) : ∀ (N : ℕ) (b : Fin N → ℕ) (c : ℝ), 0 < c →
    ∫⁻ z : Fin N → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) =
      ENNReal.ofReal (π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial /
        (∑ j, b j + N + k).factorial / c ^ (k + 1)) := by
  intro N
  induction N with
  | zero =>
    intro b c hc
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, add_zero, zero_add,
      pow_zero, one_mul]
    rw [lintegral_const, volume_pi, Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [add_comm 1 k]
    field_simp
  | succ N ih =>
    intro b c hc
    set K := ∑ j : Fin N, b j.succ + N + k with hK
    let g : ℂ × (Fin N → ℂ) → ENNReal := fun p => ENNReal.ofReal ((‖p.1‖ ^ (2 * b 0) *
        ∏ j : Fin N, ‖p.2 j‖ ^ (2 * b j.succ)) /
        (c + (‖p.1‖ ^ 2 + ∑ j : Fin N, ‖p.2 j‖ ^ 2)) ^ (b 0 + 2 + K))
    have hgm : Measurable g := by fun_prop
    have e := volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0
    have hexp : ∑ j, b j + (N + 1) + 1 + k = b 0 + 2 + K := by
      rw [Fin.sum_univ_succ, hK]; omega
    have hcomp : ∀ z : Fin (N + 1) → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + (N + 1) + 1 + k)) =
        g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0 z) := by
      intro z
      rw [hexp]
      simp [g, MeasurableEquiv.piFinSuccAbove_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.tail]
    rw [lintegral_congr hcomp, e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Measure.volume_eq_prod, lintegral_prod_symm _ hgm.aemeasurable]
    have hinner : ∀ y : Fin N → ℂ, ∫⁻ w : ℂ, g (w, y) = ENNReal.ofReal
        ((π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial) *
          ((∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ)) /
            (c + ∑ j, ‖y j‖ ^ 2) ^ (∑ j : Fin N, b j.succ + N + 1 + k))) := by
      intro y
      set A := ∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ) with hA'
      set c' := c + ∑ j, ‖y j‖ ^ 2 with hc'd
      have hc' : 0 < c' := by positivity
      have hA : 0 ≤ A := by positivity
      obtain ⟨hI, hV⟩ := integral_complex_norm_pow_div c' hc' K (b 0)
      have hsplit : ∀ w : ℂ, g (w, y) = ENNReal.ofReal A *
          ENNReal.ofReal (‖w‖ ^ (2 * b 0) / (c' + ‖w‖ ^ 2) ^ (b 0 + 2 + K)) := by
        intro w
        simp only [g]
        rw [← ENNReal.ofReal_mul hA]
        congr 1
        rw [hc'd, hA', show c + (‖w‖ ^ 2 + ∑ j, ‖y j‖ ^ 2) = c + ∑ j, ‖y j‖ ^ 2 + ‖w‖ ^ 2 by ring]
        ring
      rw [lintegral_congr hsplit, lintegral_const_mul _ (by fun_prop),
        ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun w => by positivity),
        hV, ← ENNReal.ofReal_mul hA]
      congr 1
      rw [show ∑ j : Fin N, b j.succ + N + 1 + k = K + 1 by omega]
      have : (c' ^ (K + 1)) ≠ 0 := by positivity
      field_simp
    rw [lintegral_congr hinner]
    have hC : 0 ≤ π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial := by
      positivity
    rw [lintegral_congr (fun y => ENNReal.ofReal_mul hC), lintegral_const_mul _ (by fun_prop),
      ih (fun j => b j.succ) c hc, ← ENNReal.ofReal_mul hC]
    congr 1
    rw [Fin.prod_univ_succ, show ∑ j, b j + (N + 1) + k = b 0 + K + 1 by
      rw [Fin.sum_univ_succ, hK]; omega]
    have h1 : (K.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((b 0 + K + 1).factorial : ℝ) ≠ 0 := by positivity
    have h3 : c ^ (k + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
end GroundTheory.Heights₂.Heights
