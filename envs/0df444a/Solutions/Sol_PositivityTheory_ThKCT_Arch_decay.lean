-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:55.866262+00:00
-- url     : https://prove2.me/submissions/823397cf-0d3a-45b1-9231-11ed785b4fb0

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_apply
import Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_cont
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_succ
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_add
import Theorems.Thm_PositivityTheory_ThKCT_Arch_lip_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : Y → SchwartzMap V ℂ →ₗ[ℂ] Z) (s : Y → ℝ) (hs : ∀ y, 0 ≤ s y)
    (K : ℝ) (hK : ∀ y, 0 < s y → ∃ w, ‖w‖ * s y ≤ K ∧ ∀ f, A y (S w f) = -A y f) (q : Seminorm ℂ Z)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) (M : ℕ) (hq : ∀ y f, q (A y f) ≤ (1 + s y) ^ M * p f) (N : ℕ) :
    ∃ p' : Seminorm ℂ (SchwartzMap V ℂ), Continuous p' ∧ ∀ y f, q (A y f) * (1 + s y) ^ N ≤ p' f := by
  obtain ⟨p₁, hp₁, h₁⟩ := lip_pow (M + N) p hp
  set R := max K 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  refine ⟨sc ((1 + R) ^ (M + N)) p + sc ((2 * R) ^ (M + N)) p₁,
    (sc_cont _ hp).add (sc_cont _ hp₁), fun y f => ?_⟩
  rw [Seminorm.add_apply, sc_apply (by positivity), sc_apply (by positivity)]
  have a1 := apply_nonneg p f
  have a2 := apply_nonneg p₁ f
  have a3 := hs y
  rcases le_total (s y) R with h | h
  · refine le_add_of_le_of_nonneg ?_ (by positivity)
    calc _ ≤ (1 + s y) ^ M * p f * (1 + s y) ^ N := mul_le_mul_of_nonneg_right (hq y f) (by positivity)
      _ = (1 + s y) ^ (M + N) * p f := by ring
      _ ≤ _ := by gcongr
  · refine le_add_of_nonneg_of_le (by positivity) ?_
    obtain ⟨w, hw, hA⟩ := hK y (by linarith)
    have hw' : ‖w‖ * s y ≤ R := hw.trans (le_max_left _ _)
    have hw1 : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
    have key : ∀ n : ℕ, ∀ g, q (A y g) ≤ q (A y ((fun g => S w g - g)^[n] g)) := fun n => by
      induction n with
      | zero => exact fun g => le_rfl
      | succ n ih =>
        intro g
        rw [Function.iterate_succ_apply]
        refine le_trans ?_ (ih _)
        rw [map_sub, hA, show -A y g - A y g = (-2 : ℂ) • A y g by module, map_smul_eq_mul]
        have := apply_nonneg q (A y g)
        simp only [norm_neg, Complex.norm_ofNat]
        linarith
    have h2 : ‖w‖ * (1 + s y) ≤ 2 * R := by nlinarith [norm_nonneg w]
    calc _ ≤ (1 + s y) ^ M * (‖w‖ ^ (M + N) * p₁ f) * (1 + s y) ^ N := mul_le_mul_of_nonneg_right
          ((key _ f).trans ((hq y _).trans (mul_le_mul_of_nonneg_left (h₁ w f hw1) (by positivity)))) (by positivity)
      _ = (‖w‖ * (1 + s y)) ^ (M + N) * p₁ f := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr
end PositivityTheory.ThKCT.Arch
